import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_45_0_0_0 (f : HomData π 45 0) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^4)*h20
include h6 ann in
theorem constraint_45_1_0_0 (f : HomData π 45 1) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^3)*h20
include h6 ann in
theorem constraint_45_2_0_0 (f : HomData π 45 2) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^3)*h0 + (π^4)*h20
include h6 ann in
theorem constraint_45_3_0_0 (f : HomData π 45 3) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^2)*h20
include h6 ann in
theorem constraint_45_4_0_0 (f : HomData π 45 4) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^2)*h0 + (π^3)*h20
include h6 ann in
theorem constraint_45_5_0_0 (f : HomData π 45 5) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^2)*h0 + (π^4)*h20
include h6 ann in
theorem constraint_45_6_0_0 (f : HomData π 45 6) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π)*h20
include h6 ann in
theorem constraint_45_7_0_0 (f : HomData π 45 7) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^2)*h20
include h6 ann in
theorem constraint_45_8_0_0 (f : HomData π 45 8) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^3)*h20
include h6 ann in
theorem constraint_45_9_0_0 (f : HomData π 45 9) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^4)*h20
include h6 ann in
theorem constraint_45_10_0_0 (f : HomData π 45 10) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (1)*h20
include h6 ann in
theorem constraint_45_11_0_0 (f : HomData π 45 11) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20
include h6 ann in
theorem constraint_45_12_0_0 (f : HomData π 45 12) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20
include h6 ann in
theorem constraint_45_13_0_0 (f : HomData π 45 13) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^3)*h20
include h6 ann in
theorem constraint_45_14_0_0 (f : HomData π 45 14) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^4)*h20
include h6 ann in
theorem constraint_45_15_0_0 (f : HomData π 45 15) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π^2)*h0 + (π^3)*h20
include h6 ann in
theorem constraint_45_16_0_0 (f : HomData π 45 16) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^2)*h20
include h6 ann in
theorem constraint_45_17_0_0 (f : HomData π 45 17) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^3)*h20
include h6 ann in
theorem constraint_45_18_0_0 (f : HomData π 45 18) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^2)*h20
include h6 ann in
theorem constraint_45_18_0_1 (f : HomData π 45 18) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π^2)*h0 + (π^4)*h21
include h6 ann in
theorem constraint_45_19_0_0 (f : HomData π 45 19) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (π)*h0 + (π^2)*h20
include h6 ann in
theorem constraint_45_20_0_0 (f : HomData π 45 20) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (π)*h0 + ((-1)*π^2)*h1 + (π^3)*h20
include h6 ann in
theorem constraint_45_21_0_0 (f : HomData π 45 21) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20
include h6 ann in
theorem constraint_45_22_0_0 (f : HomData π 45 22) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20
include h6 ann in
theorem constraint_45_23_0_0 (f : HomData π 45 23) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^3)*h20
include h6 ann in
theorem constraint_45_24_0_0 (f : HomData π 45 24) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20
include h6 ann in
theorem constraint_45_24_0_1 (f : HomData π 45 24) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π^2)*h0 + (π^4)*h21
include h6 ann in
theorem constraint_45_25_0_0 (f : HomData π 45 25) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20
include h6 ann in
theorem constraint_45_26_0_0 (f : HomData π 45 26) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20
include h6 ann in
theorem constraint_45_26_0_1 (f : HomData π 45 26) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21
include h6 ann in
theorem constraint_45_27_0_0 (f : HomData π 45 27) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20
include h6 ann in
theorem constraint_45_28_0_0 (f : HomData π 45 28) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20
include h6 ann in
theorem constraint_45_29_0_0 (f : HomData π 45 29) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π^2)*h1 + (π^3)*h20
include h6 ann in
theorem constraint_45_30_0_0 (f : HomData π 45 30) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20
include h6 ann in
theorem constraint_45_30_0_1 (f : HomData π 45 30) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^3)*h21
include h6 ann in
theorem constraint_45_31_0_0 (f : HomData π 45 31) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20
include h6 ann in
theorem constraint_45_31_0_1 (f : HomData π 45 31) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21
include h6 ann in
theorem constraint_45_32_0_0 (f : HomData π 45 32) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20
include h6 ann in
theorem constraint_45_32_0_1 (f : HomData π 45 32) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21
include h6 ann in
theorem constraint_45_33_0_0 (f : HomData π 45 33) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20
include h6 ann in
theorem constraint_45_34_0_0 (f : HomData π 45 34) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20
include h6 ann in
theorem constraint_45_35_0_0 (f : HomData π 45 35) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^3)*h20
include h6 ann in
theorem constraint_45_36_0_0 (f : HomData π 45 36) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20
include h6 ann in
theorem constraint_45_37_0_0 (f : HomData π 45 37) : ρ ((f.M 0 1))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20
include h6 ann in
theorem constraint_45_37_0_1 (f : HomData π 45 37) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^3)*h21
include h6 ann in
theorem constraint_45_38_0_0 (f : HomData π 45 38) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20
include h6 ann in
theorem constraint_45_38_0_1 (f : HomData π 45 38) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^3)*h21
include h6 ann in
theorem constraint_45_39_0_0 (f : HomData π 45 39) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20
include h6 ann in
theorem constraint_45_39_0_1 (f : HomData π 45 39) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h21
  norm_num at h0 h21
  linear_combination (π)*h0 + (π^4)*h21
include h6 ann in
theorem constraint_45_40_0_0 (f : HomData π 45 40) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π)*h20
include h6 ann in
theorem constraint_45_40_0_1 (f : HomData π 45 40) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (π)*h0 + ((-1)*π^2)*h1 + (π^3)*h21
include h6 ann in
theorem constraint_45_41_0_0 (f : HomData π 45 41) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h20
  norm_num at h0 h1 h20
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^2)*h20
include h6 ann in
theorem constraint_45_41_0_1 (f : HomData π 45 41) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (π)*h0 + ((-1)*π^2)*h1 + (π^4)*h21
include h6 ann in
theorem constraint_45_42_0_0 (f : HomData π 45 42) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h20
  norm_num at h1 h20
  linear_combination (1)*h1 + (π)*h20
include h6 ann in
theorem constraint_45_42_0_1 (f : HomData π 45 42) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (π)*h0 + ((-1)*π)*h1 + (π^3)*h21
include h6 ann in
theorem constraint_45_43_0_0 (f : HomData π 45 43) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h20
  norm_num at h0 h20
  linear_combination (1)*h0 + (π^2)*h20
include h6 ann in
theorem constraint_45_43_0_1 (f : HomData π 45 43) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^3)*h21
include h6 ann in
theorem constraint_45_44_0_0 (f : HomData π 45 44) : ρ ((f.M 0 2))=0 := by
  apply (ann _).mp
  have h1 := f.ambient_descent 0 1
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h20
  norm_num at h1 h20
  linear_combination (1)*h1 + (π)*h20
include h6 ann in
theorem constraint_45_44_0_1 (f : HomData π 45 44) : ρ ((f.M 0 3))=0 := by
  apply (ann _).mp
  have h0 := f.ambient_descent 0 0
  have h1 := f.ambient_descent 0 1
  have h21 := f.commutes 0 1
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h1 h21
  norm_num at h0 h1 h21
  linear_combination (1)*h0 + ((-1)*π)*h1 + (π^3)*h21
include h6 ann in
theorem constraint_45_46_0_0 (f : HomData π 45 46) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^5)*h20
end UniserialComputations.N6
