import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_10_0_0_0 (f : HomData π 10 0) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^4)*h20 + (π^3*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_1_0_0 (f : HomData π 10 1) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^3)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_2_0_0 (f : HomData π 10 2) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^3)*h0 + (π^4)*h20 + (π^3*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_3_0_0 (f : HomData π 10 3) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_4_0_0 (f : HomData π 10 4) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^2)*h0 + (π^3)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_5_0_0 (f : HomData π 10 5) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^2)*h0 + (π^4)*h20 + (π^3*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_6_0_0 (f : HomData π 10 6) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_10_7_0_0 (f : HomData π 10 7) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_8_0_0 (f : HomData π 10 8) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^3)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_9_0_0 (f : HomData π 10 9) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^4)*h20 + (π^3*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_11_0_0 (f : HomData π 10 11) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_10_12_0_0 (f : HomData π 10 12) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_13_0_0 (f : HomData π 10 13) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^3)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_14_0_0 (f : HomData π 10 14) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^4)*h20 + (π^3*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_15_0_0 (f : HomData π 10 15) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^2)*h0 + (π^3)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_16_0_0 (f : HomData π 10 16) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_17_0_0 (f : HomData π 10 17) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^3)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_18_0_0 (f : HomData π 10 18) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_18_0_1 (f : HomData π 10 18) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π^2)*h0 + (π^4)*h21 + (π^3*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_19_0_0 (f : HomData π 10 19) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_20_0_0 (f : HomData π 10 20) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (π)*h0 + ((-1)*π^2)*h1 + (π^3)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_21_0_0 (f : HomData π 10 21) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_10_22_0_0 (f : HomData π 10 22) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_23_0_0 (f : HomData π 10 23) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^3)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_24_0_0 (f : HomData π 10 24) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_10_24_0_1 (f : HomData π 10 24) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π^2)*h0 + (π^4)*h21 + (π^3*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_25_0_0 (f : HomData π 10 25) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_10_26_0_0 (f : HomData π 10 26) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_26_0_1 (f : HomData π 10 26) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21 + (π^3*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_27_0_0 (f : HomData π 10 27) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_28_0_0 (f : HomData π 10 28) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_29_0_0 (f : HomData π 10 29) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π^2)*h1 + (π^3)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_30_0_0 (f : HomData π 10 30) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_10_30_0_1 (f : HomData π 10 30) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^3)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_31_0_0 (f : HomData π 10 31) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_10_31_0_1 (f : HomData π 10 31) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21 + (π^3*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_32_0_0 (f : HomData π 10 32) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_32_0_1 (f : HomData π 10 32) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21 + (π^3*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_33_0_0 (f : HomData π 10 33) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_10_34_0_0 (f : HomData π 10 34) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_35_0_0 (f : HomData π 10 35) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^3)*h20 + (π^2*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_36_0_0 (f : HomData π 10 36) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_37_0_0 (f : HomData π 10 37) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_10_37_0_1 (f : HomData π 10 37) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^3)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_38_0_0 (f : HomData π 10 38) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_38_0_1 (f : HomData π 10 38) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^3)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_39_0_0 (f : HomData π 10 39) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_39_0_1 (f : HomData π 10 39) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21 + (π^3*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_40_0_0 (f : HomData π 10 40) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_10_40_0_1 (f : HomData π 10 40) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (π)*h0 + ((-1)*π^2)*h1 + (π^3)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_41_0_0 (f : HomData π 10 41) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_41_0_1 (f : HomData π 10 41) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (π)*h0 + ((-1)*π^2)*h1 + (π^4)*h21 + (π^3*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_42_0_0 (f : HomData π 10 42) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h20
  norm_num at h1 h20
  linear_combination (1)*h1 + (π)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_10_42_0_1 (f : HomData π 10 42) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (π)*h0 + ((-1)*π)*h1 + (π^3)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_43_0_0 (f : HomData π 10 43) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20 + (π*(f.U 0 0))*h6
include h6 ann in
theorem constraint_10_43_0_1 (f : HomData π 10 43) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^3)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_44_0_0 (f : HomData π 10 44) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h20
  norm_num at h1 h20
  linear_combination (1)*h1 + (π)*h20 + ((f.U 0 0))*h6
include h6 ann in
theorem constraint_10_44_0_1 (f : HomData π 10 44) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^3)*h21 + (π^2*(f.U 0 1))*h6
include h6 ann in
theorem constraint_10_46_0_0 (f : HomData π 10 46) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^5)*h20 + (π^4*(f.U 0 0))*h6
end UniserialComputations.N6
