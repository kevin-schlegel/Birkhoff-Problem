import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_35_0_0_0 (f : HomData π 35 0) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_35_1_0_0 (f : HomData π 35 1) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h24
  norm_num at h20 h24
  linear_combination (π^2)*h20 + (π^3)*h24 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_35_2_0_0 (f : HomData π 35 2) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^3)*h8 + (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_35_3_0_0 (f : HomData π 35 3) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h24
  norm_num at h20 h24
  linear_combination (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_35_4_0_0 (f : HomData π 35 4) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (π)*h0 + (π^2)*h8 + (π^2)*h20 + (π^3)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_35_5_0_0 (f : HomData π 35 5) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π^2)*h8 + (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_35_6_0_0 (f : HomData π 35 6) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20 h24
  norm_num at h20 h24
  linear_combination (1)*h20 + (π)*h24 + ((-1)*(f.M 0 0))*h6
include h6 ann in
theorem constraint_35_7_0_0 (f : HomData π 35 7) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_35_8_0_0 (f : HomData π 35 8) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π^2)*h20 + (π^3)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_35_9_0_0 (f : HomData π 35 9) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (π)*h8 + (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_35_14_0_0 (f : HomData π 35 14) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h24
  norm_num at h8 h24
  linear_combination (1)*h8 + (π^4)*h24 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_35_15_0_0 (f : HomData π 35 15) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (π)*h0 + (π^2)*h8 + (π^2)*h20 + (π^3)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_35_16_0_0 (f : HomData π 35 16) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_35_17_0_0 (f : HomData π 35 17) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π^2)*h20 + (π^3)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_35_18_0_0 (f : HomData π 35 18) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_35_18_0_1 (f : HomData π 35 18) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_35_19_0_0 (f : HomData π 35 19) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h20 := f.commutes 0 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h20 h24
  norm_num at h0 h8 h20 h24
  linear_combination (1)*h0 + (π)*h8 + (π)*h20 + (π^2)*h24 + ((-1)*(f.M 0 1))*h6
include h6 ann in
theorem constraint_35_20_0_0 (f : HomData π 35 20) : ρ ((f.M 2 2))=0 := by
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
theorem constraint_35_23_0_0 (f : HomData π 35 23) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h22 h24
  norm_num at h8 h22 h24
  linear_combination (1)*h8 + ((-1)*π)*h22 + (π^3)*h24 + ((-1)*(f.M 1 0) + π*(f.M 1 1))*h6
include h6 ann in
theorem constraint_35_24_0_1 (f : HomData π 35 24) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π^2)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_35_26_0_1 (f : HomData π 35 26) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_35_28_0_0 (f : HomData π 35 28) : ρ ((f.M 2 1))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h22 h24
  norm_num at h8 h22 h24
  linear_combination (1)*h8 + ((-1))*h22 + (π^2)*h24 + ((-1)*(f.M 1 0) + π*(f.M 1 1))*h6
include h6 ann in
theorem constraint_35_29_0_0 (f : HomData π 35 29) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h5 := f.ambient_descent 1 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h5 h8 h9 h22 h24
  norm_num at h5 h8 h9 h22 h24
  linear_combination (1)*h5 + (1)*h8 + ((-1)*π^2)*h9 + ((-1)*π)*h22 + (π^3)*h24 + ((-1)*(f.M 1 0) + π*(f.M 1 2))*h6
include h6 ann in
theorem constraint_35_30_0_1 (f : HomData π 35 30) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h21 h25
  norm_num at h0 h8 h21 h25
  linear_combination (1)*h0 + (π)*h8 + (π^2)*h21 + (π^3)*h25 + ((-1)*(f.M 0 2))*h6
include h6 ann in
theorem constraint_35_31_0_1 (f : HomData π 35 31) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_35_32_0_1 (f : HomData π 35 32) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_35_37_0_1 (f : HomData π 35 37) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h21 h25
  norm_num at h0 h8 h21 h25
  linear_combination (1)*h0 + (π)*h8 + (π^2)*h21 + (π^3)*h25 + ((-1)*(f.M 0 2))*h6
include h6 ann in
theorem constraint_35_38_0_1 (f : HomData π 35 38) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h8 := f.ambient_descent 2 0
  have h21 := f.commutes 0 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h8 h21 h25
  norm_num at h0 h8 h21 h25
  linear_combination (1)*h0 + (π)*h8 + (π^2)*h21 + (π^3)*h25 + ((-1)*(f.M 0 3))*h6
include h6 ann in
theorem constraint_35_39_0_1 (f : HomData π 35 39) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h25
  norm_num at h8 h25
  linear_combination (π)*h8 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_35_40_0_1 (f : HomData π 35 40) : ρ ((f.M 2 3))=0 := by
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
theorem constraint_35_41_0_1 (f : HomData π 35 41) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h25
  norm_num at h8 h9 h25
  linear_combination (π)*h8 + ((-1)*π^2)*h9 + (π^4)*h25 + ((f.U 0 1))*h6
include h6 ann in
theorem constraint_35_42_0_1 (f : HomData π 35 42) : ρ ((f.M 2 3))=0 := by
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
theorem constraint_35_43_0_0 (f : HomData π 35 43) : ρ ((f.M 2 2))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h22 := f.commutes 1 0
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h22 h24
  norm_num at h8 h22 h24
  linear_combination (1)*h8 + ((-1))*h22 + (π^2)*h24 + ((-1)*(f.M 1 0) + π*(f.M 1 2))*h6
include h6 ann in
theorem constraint_35_43_0_1 (f : HomData π 35 43) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h20 := f.commutes 0 0
  have h21 := f.commutes 0 1
  have h22 := f.commutes 1 0
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h8 h9 h20 h21 h22 h25
  norm_num at h1 h8 h9 h20 h21 h22 h25
  linear_combination ((-1))*h1 + (1)*h8 + ((-1)*π)*h9 + ((-1)*π)*h20 + (π^2)*h21 + ((-1))*h22 + (π^3)*h25 + ((f.M 0 2) + (-1)*(f.M 0 3) + (-1)*(f.M 1 0) + π*(f.M 1 2))*h6
include h6 ann in
theorem constraint_35_44_0_1 (f : HomData π 35 44) : ρ ((f.M 2 3))=0 := by
  apply (ann _).mp
  have h8 := f.ambient_descent 2 0
  have h9 := f.ambient_descent 2 1
  have h16 := f.source_descent 0 0
  have h22 := f.commutes 1 0
  have h23 := f.commutes 1 1
  have h25 := f.commutes 2 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h8 h9 h16 h22 h23 h25
  norm_num at h8 h9 h16 h22 h23 h25
  linear_combination (1)*h8 + ((-1)*π)*h9 + ((-1))*h16 + ((-1))*h22 + ((-1)*π)*h23 + (π^3)*h25 + ((-1)*(f.M 1 0) + π^2*(f.M 1 2) + π*(f.M 1 3))*h6
include h6 ann in
theorem constraint_35_46_0_0 (f : HomData π 35 46) : ρ ((f.M 2 0))=0 := by
  apply (ann _).mp
  have h24 := f.commutes 2 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h24
  norm_num at h24
  linear_combination (π^5)*h24 + (π*(f.U 0 0))*h6
end UniserialComputations.N6
