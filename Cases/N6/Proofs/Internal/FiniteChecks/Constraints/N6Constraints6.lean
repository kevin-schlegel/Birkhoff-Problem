import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_6_0_0_0 (f : HomData π 6 0) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^4)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_1_0_0 (f : HomData π 6 1) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^3)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_2_0_0 (f : HomData π 6 2) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^3)*h0 + (π^4)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_3_0_0 (f : HomData π 6 3) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_4_0_0 (f : HomData π 6 4) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^2)*h0 + (π^3)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_5_0_0 (f : HomData π 6 5) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^2)*h0 + (π^4)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_7_0_0 (f : HomData π 6 7) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_8_0_0 (f : HomData π 6 8) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^3)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_9_0_0 (f : HomData π 6 9) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^4)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_12_0_0 (f : HomData π 6 12) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_13_0_0 (f : HomData π 6 13) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^3)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_14_0_0 (f : HomData π 6 14) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^4)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_15_0_0 (f : HomData π 6 15) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^2)*h0 + (π^3)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_16_0_0 (f : HomData π 6 16) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_17_0_0 (f : HomData π 6 17) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^3)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_18_0_0 (f : HomData π 6 18) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_18_0_1 (f : HomData π 6 18) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π^2)*h0 + (π^4)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_19_0_0 (f : HomData π 6 19) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_20_0_0 (f : HomData π 6 20) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (π)*h0 + ((-1)*π^2)*h1 + (π^3)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_22_0_0 (f : HomData π 6 22) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_23_0_0 (f : HomData π 6 23) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^3)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_24_0_1 (f : HomData π 6 24) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π^2)*h0 + (π^4)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_26_0_0 (f : HomData π 6 26) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_26_0_1 (f : HomData π 6 26) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_27_0_0 (f : HomData π 6 27) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_28_0_0 (f : HomData π 6 28) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_29_0_0 (f : HomData π 6 29) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π^2)*h1 + (π^3)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_30_0_1 (f : HomData π 6 30) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^3)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_31_0_1 (f : HomData π 6 31) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_32_0_0 (f : HomData π 6 32) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_32_0_1 (f : HomData π 6 32) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_34_0_0 (f : HomData π 6 34) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_35_0_0 (f : HomData π 6 35) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^3)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_6_36_0_0 (f : HomData π 6 36) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_37_0_1 (f : HomData π 6 37) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^3)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_38_0_0 (f : HomData π 6 38) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_38_0_1 (f : HomData π 6 38) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^3)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_39_0_0 (f : HomData π 6 39) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_39_0_1 (f : HomData π 6 39) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_40_0_1 (f : HomData π 6 40) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (π)*h0 + ((-1)*π^2)*h1 + (π^3)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_41_0_0 (f : HomData π 6 41) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_41_0_1 (f : HomData π 6 41) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (π)*h0 + ((-1)*π^2)*h1 + (π^4)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_42_0_1 (f : HomData π 6 42) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (π)*h0 + ((-1)*π)*h1 + (π^3)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_43_0_0 (f : HomData π 6 43) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_6_43_0_1 (f : HomData π 6 43) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^3)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_44_0_1 (f : HomData π 6 44) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^3)*h21 + (π*(f.U 0 1))*h6
include h6 ann in
theorem constraint_6_46_0_0 (f : HomData π 6 46) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^5)*h20 + (π^3*(f.U 0 0))*h6
end UniserialComputations.N6
