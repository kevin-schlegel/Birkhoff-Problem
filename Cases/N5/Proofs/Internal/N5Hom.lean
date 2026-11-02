import N5Quiver
noncomputable section
namespace UniserialComputations.N5
namespace Raw
set_option maxHeartbeats 8000000
def ell : Fin 18 → Fin 3 → Nat := ![![5,0,0],![5,0,0],![5,0,0],![5,0,0],![5,0,0],![5,0,0],![5,1,0],![5,1,0],![5,1,0],![5,2,0],![5,2,0],![5,2,0],![5,2,0],![5,3,0],![5,3,0],![5,3,0],![5,3,1],![5,5,2]]
def src : Fin 18 → Fin 2 → Nat := ![![0,0],![1,0],![2,0],![3,0],![4,0],![5,0],![2,0],![3,0],![4,0],![2,0],![3,0],![3,0],![4,0],![2,0],![3,0],![4,0],![3,0],![4,2]]
def gen : Fin 18 → Fin 3 → Fin 2 → Nat := ![![![5,5],![5,5],![5,5]],![![4,5],![5,5],![5,5]],![![3,5],![5,5],![5,5]],![![2,5],![5,5],![5,5]],![![1,5],![5,5],![5,5]],![![0,5],![5,5],![5,5]],![![3,5],![0,5],![5,5]],![![2,5],![0,5],![5,5]],![![1,5],![0,5],![5,5]],![![3,5],![1,5],![5,5]],![![2,5],![0,5],![5,5]],![![2,5],![1,5],![5,5]],![![1,5],![0,5],![5,5]],![![3,5],![2,5],![5,5]],![![2,5],![1,5],![5,5]],![![1,5],![0,5],![5,5]],![![2,5],![1,5],![0,5]],![![5,3],![1,5],![0,1]]]
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h5 : π^5=0) (ann : ∀ r, π^4*r=0 ↔ ρ r=0)
def ambient (i j : Fin 18) (v : Fin 13 → R) : Matrix (Fin 3) (Fin 3) R :=
  fun r c => π^(ell i r-ell j c)*v ⟨r.val*3+c.val,by omega⟩
def source (i j : Fin 18) (v : Fin 13 → R) : Matrix (Fin 2) (Fin 2) R :=
  fun r c => π^(src i r-src j c)*v ⟨9+r.val*2+c.val,by omega⟩
def embedding (i : Fin 18) : Matrix (Fin 3) (Fin 2) R := fun r c => π^(gen i r c)
def equation (i j : Fin 18) (v : Fin 13 → R) (r : Fin 3) (c : Fin 2) : R :=
  π^(5-ell i r)*((ambient π i j v*embedding π j) r c-(embedding π i*source π i j v) r c)
/-- A matrix morphism j→i, with cyclic-summand descent built into the powers of π.
The six equations express its commuting square modulo each target summand. -/
structure HomData (i j : Fin 18) where
  v : Fin 13 → R
  commutes : ∀ r c, equation π i j v r c=0
include h5 ann in
theorem image_0_1_0 (f : HomData π 0 1) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (1)*h0 + (-π^5*(f.v 1) - π^5*(f.v 2) + (f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_0_2_0 (f : HomData π 0 2) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π)*h0 + (-π^6*(f.v 1) - π^6*(f.v 2) + π*(f.v 11) + π*(f.v 9))*h5
include h5 ann in
theorem image_0_3_0 (f : HomData π 0 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^2*(f.v 11) + π^2*(f.v 9))*h5
include h5 ann in
theorem image_0_4_0 (f : HomData π 0 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^3*(f.v 11) + π^3*(f.v 9))*h5
include h5 ann in
theorem image_0_5_0 (f : HomData π 0 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + π^4*(f.v 9))*h5
include h5 ann in
theorem image_0_6_0 (f : HomData π 0 6) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π)*h0 + (-π^6*(f.v 2) + π*(f.v 11) + π*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_0_7_0 (f : HomData π 0 7) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) + π^2*(f.v 9) - π*(f.v 1))*h5
include h5 ann in
theorem image_0_8_0 (f : HomData π 0 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) + π^3*(f.v 9) - π^2*(f.v 1))*h5
include h5 ann in
theorem image_0_9_0 (f : HomData π 0 9) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π)*h0 + (-π^6*(f.v 2) + π*(f.v 11) + π*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_0_10_0 (f : HomData π 0 10) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) + π^2*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_0_11_0 (f : HomData π 0 11) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) + π^2*(f.v 9) - π*(f.v 1))*h5
include h5 ann in
theorem image_0_12_0 (f : HomData π 0 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) + π^3*(f.v 9) - π*(f.v 1))*h5
include h5 ann in
theorem image_0_13_0 (f : HomData π 0 13) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π)*h0 + (-π^6*(f.v 2) + π*(f.v 11) + π*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_0_14_0 (f : HomData π 0 14) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) + π^2*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_0_15_0 (f : HomData π 0 15) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) + π^3*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_0_16_0 (f : HomData π 0 16) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (π^2*(f.v 11) + π^2*(f.v 9) - π*(f.v 2) - (f.v 1))*h5
include h5 ann in
theorem image_0_17_0 (f : HomData π 0 17) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h1 := f.commutes 0 1
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h1
  norm_num at h1
  linear_combination (π)*h1 + (-π*(f.v 1) + π*(f.v 10) + π*(f.v 12) - (f.v 2))*h5
include h5 ann in
theorem image_0_17_1 (f : HomData π 0 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^3*(f.v 0) + π^3*(f.v 11) + π^3*(f.v 9) - π*(f.v 2))*h5
include h5 ann in
theorem image_1_2_0 (f : HomData π 1 2) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π)*h0 + (-π^6*(f.v 1) - π^6*(f.v 2) + π*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_1_3_0 (f : HomData π 1 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^2*(f.v 11) + π*(f.v 9))*h5
include h5 ann in
theorem image_1_4_0 (f : HomData π 1 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^3*(f.v 11) + π^2*(f.v 9))*h5
include h5 ann in
theorem image_1_5_0 (f : HomData π 1 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + π^3*(f.v 9))*h5
include h5 ann in
theorem image_1_6_0 (f : HomData π 1 6) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π)*h0 + (-π^6*(f.v 2) + π*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_1_7_0 (f : HomData π 1 7) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - π*(f.v 1) + π*(f.v 9))*h5
include h5 ann in
theorem image_1_8_0 (f : HomData π 1 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π^2*(f.v 1) + π^2*(f.v 9))*h5
include h5 ann in
theorem image_1_9_0 (f : HomData π 1 9) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π)*h0 + (-π^6*(f.v 2) + π*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_1_10_0 (f : HomData π 1 10) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) + π*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_1_11_0 (f : HomData π 1 11) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - π*(f.v 1) + π*(f.v 9))*h5
include h5 ann in
theorem image_1_12_0 (f : HomData π 1 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) + π^2*(f.v 9) - π*(f.v 1))*h5
include h5 ann in
theorem image_1_13_0 (f : HomData π 1 13) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π)*h0 + (-π^6*(f.v 2) + π*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_1_14_0 (f : HomData π 1 14) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) + π*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_1_15_0 (f : HomData π 1 15) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) + π^2*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_1_16_0 (f : HomData π 1 16) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (π^2*(f.v 11) - π*(f.v 2) + π*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_1_17_0 (f : HomData π 1 17) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h1 := f.commutes 0 1
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h1
  norm_num at h1
  linear_combination (π)*h1 + (-π*(f.v 1) + π*(f.v 12) + (f.v 10) - (f.v 2))*h5
include h5 ann in
theorem image_1_17_1 (f : HomData π 1 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^3*(f.v 0) + π^3*(f.v 11) + π^2*(f.v 9) - π*(f.v 2))*h5
include h5 ann in
theorem image_2_3_0 (f : HomData π 2 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^2*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_2_4_0 (f : HomData π 2 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^3*(f.v 11) + π*(f.v 9))*h5
include h5 ann in
theorem image_2_5_0 (f : HomData π 2 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + π^2*(f.v 9))*h5
include h5 ann in
theorem image_2_7_0 (f : HomData π 2 7) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_2_8_0 (f : HomData π 2 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π^2*(f.v 1) + π*(f.v 9))*h5
include h5 ann in
theorem image_2_10_0 (f : HomData π 2 10) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_2_11_0 (f : HomData π 2 11) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_2_12_0 (f : HomData π 2 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π*(f.v 1) + π*(f.v 9))*h5
include h5 ann in
theorem image_2_14_0 (f : HomData π 2 14) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_2_15_0 (f : HomData π 2 15) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) + π*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_2_16_0 (f : HomData π 2 16) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (π^2*(f.v 11) - π*(f.v 2) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_2_17_0 (f : HomData π 2 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^3*(f.v 0) + π^3*(f.v 11) - π*(f.v 2) + π*(f.v 9))*h5
include h5 ann in
theorem image_3_4_0 (f : HomData π 3 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^3*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_3_5_0 (f : HomData π 3 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + π*(f.v 9))*h5
include h5 ann in
theorem image_3_8_0 (f : HomData π 3 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π^2*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_3_12_0 (f : HomData π 3 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_3_15_0 (f : HomData π 3 15) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_3_17_0 (f : HomData π 3 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^3*(f.v 0) + π^3*(f.v 11) - π*(f.v 2) + (f.v 9))*h5
include h5 ann in
theorem image_4_5_0 (f : HomData π 4 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_6_2_0 (f : HomData π 6 2) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π)*h0 + (-1)*h2 + (-π^6*(f.v 1) - π^6*(f.v 2) + π^5*(f.v 4) + π^5*(f.v 5) - π^4*(f.v 11) + π^2*(f.v 3) + π*(f.v 11))*h5
include h5 ann in
theorem image_6_3_0 (f : HomData π 6 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^2*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_6_4_0 (f : HomData π 6 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^3*(f.v 11) + π*(f.v 9))*h5
include h5 ann in
theorem image_6_5_0 (f : HomData π 6 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + π^2*(f.v 9))*h5
include h5 ann in
theorem image_6_7_0 (f : HomData π 6 7) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_6_8_0 (f : HomData π 6 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π^2*(f.v 1) + π*(f.v 9))*h5
include h5 ann in
theorem image_6_9_0 (f : HomData π 6 9) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π)*h0 + (-1)*h2 + (-π^6*(f.v 2) + π^5*(f.v 5) - π^4*(f.v 11) + π^2*(f.v 3) + π*(f.v 11) - (f.v 1) + (f.v 4))*h5
include h5 ann in
theorem image_6_10_0 (f : HomData π 6 10) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_6_11_0 (f : HomData π 6 11) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_6_12_0 (f : HomData π 6 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π*(f.v 1) + π*(f.v 9))*h5
include h5 ann in
theorem image_6_13_0 (f : HomData π 6 13) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π)*h0 + (-1)*h2 + (-π^6*(f.v 2) + π^5*(f.v 5) - π^4*(f.v 11) + π^2*(f.v 3) + π*(f.v 11) + π*(f.v 4) - (f.v 1))*h5
include h5 ann in
theorem image_6_14_0 (f : HomData π 6 14) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_6_15_0 (f : HomData π 6 15) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) + π*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_6_16_0 (f : HomData π 6 16) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (π^2*(f.v 11) - π*(f.v 2) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_6_17_0 (f : HomData π 6 17) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h1 := f.commutes 0 1
  have h3 := f.commutes 1 1
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h3
  norm_num at h1 h3
  linear_combination (π)*h1 + (-1)*h3 + (-π^4*(f.v 12) + π^4*(f.v 4) + π^2*(f.v 3) - π*(f.v 1) + π*(f.v 12) - (f.v 2) + (f.v 5))*h5
include h5 ann in
theorem image_6_17_1 (f : HomData π 6 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^3*(f.v 0) + π^3*(f.v 11) - π*(f.v 2) + π*(f.v 9))*h5
include h5 ann in
theorem image_7_3_0 (f : HomData π 7 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-1)*h2 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^5*(f.v 4) + π^5*(f.v 5) - π^4*(f.v 11) + π^2*(f.v 11) + π*(f.v 3))*h5
include h5 ann in
theorem image_7_4_0 (f : HomData π 7 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^3*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_7_5_0 (f : HomData π 7 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + π*(f.v 9))*h5
include h5 ann in
theorem image_7_8_0 (f : HomData π 7 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π^2*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_7_11_0 (f : HomData π 7 11) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-1)*h2 + (-π^7*(f.v 2) + π^5*(f.v 5) - π^4*(f.v 11) + π^2*(f.v 11) - π*(f.v 1) + π*(f.v 3) + (f.v 4))*h5
include h5 ann in
theorem image_7_12_0 (f : HomData π 7 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_7_14_0 (f : HomData π 7 14) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-1)*h2 + (-π^7*(f.v 2) + π^5*(f.v 5) - π^4*(f.v 11) + π^2*(f.v 11) + π*(f.v 3) - (f.v 1) + (f.v 4))*h5
include h5 ann in
theorem image_7_15_0 (f : HomData π 7 15) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_7_17_0 (f : HomData π 7 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^3*(f.v 0) + π^3*(f.v 11) - π*(f.v 2) + (f.v 9))*h5
include h5 ann in
theorem image_8_4_0 (f : HomData π 8 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^3)*h0 + (-1)*h2 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^5*(f.v 4) + π^5*(f.v 5) - π^4*(f.v 11) + π^3*(f.v 11) + (f.v 3))*h5
include h5 ann in
theorem image_8_5_0 (f : HomData π 8 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_9_2_0 (f : HomData π 9 2) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π)*h0 + (-1)*h2 + (-π^6*(f.v 1) - π^6*(f.v 2) + π^5*(f.v 4) + π^5*(f.v 5) - π^3*(f.v 11) + π*(f.v 11) + π*(f.v 3))*h5
include h5 ann in
theorem image_9_3_0 (f : HomData π 9 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^2*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_9_4_0 (f : HomData π 9 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^3*(f.v 11) + π*(f.v 9))*h5
include h5 ann in
theorem image_9_5_0 (f : HomData π 9 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + π^2*(f.v 9))*h5
include h5 ann in
theorem image_9_7_0 (f : HomData π 9 7) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_9_8_0 (f : HomData π 9 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π^2*(f.v 1) + π*(f.v 9))*h5
include h5 ann in
theorem image_9_10_0 (f : HomData π 9 10) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_9_11_0 (f : HomData π 9 11) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_9_12_0 (f : HomData π 9 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π*(f.v 1) + π*(f.v 9))*h5
include h5 ann in
theorem image_9_13_0 (f : HomData π 9 13) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π)*h0 + (-1)*h2 + (-π^6*(f.v 2) + π^5*(f.v 5) - π^3*(f.v 11) + π*(f.v 11) + π*(f.v 3) - (f.v 1) + (f.v 4))*h5
include h5 ann in
theorem image_9_14_0 (f : HomData π 9 14) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_9_15_0 (f : HomData π 9 15) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) + π*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_9_16_0 (f : HomData π 9 16) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (π^2*(f.v 11) - π*(f.v 2) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_9_17_0 (f : HomData π 9 17) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h1 := f.commutes 0 1
  have h2 := f.commutes 1 0
  have h3 := f.commutes 1 1
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h2 h3
  norm_num at h1 h2 h3
  linear_combination (π)*h1 + (π)*h2 + (-1)*h3 + (π^4*(f.v 11) - π^4*(f.v 3) - π^3*(f.v 12) + π^3*(f.v 4) - π*(f.v 1) + π*(f.v 12) + π*(f.v 3) - (f.v 2) - (f.v 4) + (f.v 9))*h5
include h5 ann in
theorem image_9_17_1 (f : HomData π 9 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^3*(f.v 0) + π^3*(f.v 11) - π*(f.v 2) + π*(f.v 9))*h5
include h5 ann in
theorem image_10_2_0 (f : HomData π 10 2) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π)*h0 + (-1)*h2 + (-π^6*(f.v 1) - π^6*(f.v 2) + π^5*(f.v 4) + π^5*(f.v 5) - π^3*(f.v 11) + π*(f.v 11) + π*(f.v 3))*h5
include h5 ann in
theorem image_10_3_0 (f : HomData π 10 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^6*(f.v 4) + π^6*(f.v 5) - π^4*(f.v 11) + π^2*(f.v 11) + π*(f.v 3))*h5
include h5 ann in
theorem image_10_4_0 (f : HomData π 10 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^3*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_10_5_0 (f : HomData π 10 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + π*(f.v 9))*h5
include h5 ann in
theorem image_10_7_0 (f : HomData π 10 7) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^7*(f.v 2) + π^6*(f.v 5) - π^4*(f.v 11) + π^2*(f.v 11) - π*(f.v 1) + π*(f.v 3) + (f.v 4))*h5
include h5 ann in
theorem image_10_8_0 (f : HomData π 10 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π^2*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_10_11_0 (f : HomData π 10 11) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^7*(f.v 2) + π^6*(f.v 5) - π^4*(f.v 11) + π^2*(f.v 11) - π*(f.v 1) + π*(f.v 3) + (f.v 4))*h5
include h5 ann in
theorem image_10_12_0 (f : HomData π 10 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_10_13_0 (f : HomData π 10 13) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π)*h0 + (-1)*h2 + (-π^6*(f.v 2) + π^5*(f.v 5) - π^3*(f.v 11) + π*(f.v 11) + π*(f.v 3) - (f.v 1) + (f.v 4))*h5
include h5 ann in
theorem image_10_14_0 (f : HomData π 10 14) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^7*(f.v 2) + π^6*(f.v 5) - π^4*(f.v 11) + π^2*(f.v 11) + π*(f.v 3) - (f.v 1) + (f.v 4))*h5
include h5 ann in
theorem image_10_15_0 (f : HomData π 10 15) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_10_16_0 (f : HomData π 10 16) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^4*(f.v 11) + π^2*(f.v 11) - π*(f.v 2) + π*(f.v 3) - (f.v 1) + (f.v 4) + (f.v 5))*h5
include h5 ann in
theorem image_10_17_0 (f : HomData π 10 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^3*(f.v 0) + π^3*(f.v 11) - π*(f.v 2) + (f.v 9))*h5
include h5 ann in
theorem image_11_3_0 (f : HomData π 11 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-1)*h2 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^5*(f.v 4) + π^5*(f.v 5) - π^3*(f.v 11) + π^2*(f.v 11) + (f.v 3))*h5
include h5 ann in
theorem image_11_4_0 (f : HomData π 11 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^3*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_11_5_0 (f : HomData π 11 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + π*(f.v 9))*h5
include h5 ann in
theorem image_11_8_0 (f : HomData π 11 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π^2*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_11_12_0 (f : HomData π 11 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_11_15_0 (f : HomData π 11 15) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_11_17_0 (f : HomData π 11 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^3*(f.v 0) + π^3*(f.v 11) - π*(f.v 2) + (f.v 9))*h5
include h5 ann in
theorem image_12_3_0 (f : HomData π 12 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-1)*h2 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^5*(f.v 4) + π^5*(f.v 5) - π^3*(f.v 11) + π^2*(f.v 11) + (f.v 3))*h5
include h5 ann in
theorem image_12_4_0 (f : HomData π 12 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^3)*h0 + (-π)*h2 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^6*(f.v 4) + π^6*(f.v 5) - π^4*(f.v 11) + π^3*(f.v 11) + (f.v 3))*h5
include h5 ann in
theorem image_12_5_0 (f : HomData π 12 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_12_8_0 (f : HomData π 12 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^3)*h0 + (-π)*h2 + (-π^8*(f.v 2) + π^6*(f.v 5) - π^4*(f.v 11) + π^3*(f.v 11) - π^2*(f.v 1) + (f.v 3) + (f.v 4))*h5
include h5 ann in
theorem image_12_17_0 (f : HomData π 12 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  have h3 := f.commutes 1 1
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2 h3
  norm_num at h0 h2 h3
  linear_combination (π^3)*h0 + (-π)*h2 + (1)*h3 + (-π^4*(f.v 11) + π^4*(f.v 3) - π^3*(f.v 0) + π^3*(f.v 11) + π^3*(f.v 12) - π^3*(f.v 4) - π*(f.v 2) - π*(f.v 3) + (f.v 10) + (f.v 4))*h5
include h5 ann in
theorem image_13_2_0 (f : HomData π 13 2) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π)*h0 + (-1)*h2 + (-π^6*(f.v 1) - π^6*(f.v 2) + π^5*(f.v 4) + π^5*(f.v 5) - π^2*(f.v 11) + π*(f.v 11) + (f.v 3))*h5
include h5 ann in
theorem image_13_3_0 (f : HomData π 13 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^2*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_13_4_0 (f : HomData π 13 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^3*(f.v 11) + π*(f.v 9))*h5
include h5 ann in
theorem image_13_5_0 (f : HomData π 13 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + π^2*(f.v 9))*h5
include h5 ann in
theorem image_13_7_0 (f : HomData π 13 7) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_13_8_0 (f : HomData π 13 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π^2*(f.v 1) + π*(f.v 9))*h5
include h5 ann in
theorem image_13_10_0 (f : HomData π 13 10) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_13_11_0 (f : HomData π 13 11) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_13_12_0 (f : HomData π 13 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π*(f.v 1) + π*(f.v 9))*h5
include h5 ann in
theorem image_13_14_0 (f : HomData π 13 14) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^2*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_13_15_0 (f : HomData π 13 15) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) + π*(f.v 9) - (f.v 1))*h5
include h5 ann in
theorem image_13_16_0 (f : HomData π 13 16) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (π^2*(f.v 11) - π*(f.v 2) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_13_17_0 (f : HomData π 13 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^3*(f.v 0) + π^3*(f.v 11) - π*(f.v 2) + π*(f.v 9))*h5
include h5 ann in
theorem image_14_2_0 (f : HomData π 14 2) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π)*h0 + (-1)*h2 + (-π^6*(f.v 1) - π^6*(f.v 2) + π^5*(f.v 4) + π^5*(f.v 5) - π^2*(f.v 11) + π*(f.v 11) + (f.v 3))*h5
include h5 ann in
theorem image_14_3_0 (f : HomData π 14 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^6*(f.v 4) + π^6*(f.v 5) - π^3*(f.v 11) + π^2*(f.v 11) + (f.v 3))*h5
include h5 ann in
theorem image_14_4_0 (f : HomData π 14 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^3*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_14_5_0 (f : HomData π 14 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + π*(f.v 9))*h5
include h5 ann in
theorem image_14_7_0 (f : HomData π 14 7) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^7*(f.v 2) + π^6*(f.v 5) - π^3*(f.v 11) + π^2*(f.v 11) - π*(f.v 1) + (f.v 3) + (f.v 4))*h5
include h5 ann in
theorem image_14_8_0 (f : HomData π 14 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π^2*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_14_11_0 (f : HomData π 14 11) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^7*(f.v 2) + π^6*(f.v 5) - π^3*(f.v 11) + π^2*(f.v 11) - π*(f.v 1) + (f.v 3) + (f.v 4))*h5
include h5 ann in
theorem image_14_12_0 (f : HomData π 14 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_14_15_0 (f : HomData π 14 15) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_14_17_0 (f : HomData π 14 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^3*(f.v 0) + π^3*(f.v 11) - π*(f.v 2) + (f.v 9))*h5
include h5 ann in
theorem image_15_2_0 (f : HomData π 15 2) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π)*h0 + (-1)*h2 + (-π^6*(f.v 1) - π^6*(f.v 2) + π^5*(f.v 4) + π^5*(f.v 5) - π^2*(f.v 11) + π*(f.v 11) + (f.v 3))*h5
include h5 ann in
theorem image_15_3_0 (f : HomData π 15 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^6*(f.v 4) + π^6*(f.v 5) - π^3*(f.v 11) + π^2*(f.v 11) + (f.v 3))*h5
include h5 ann in
theorem image_15_4_0 (f : HomData π 15 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^3)*h0 + (-π^2)*h2 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^7*(f.v 4) + π^7*(f.v 5) - π^4*(f.v 11) + π^3*(f.v 11) + (f.v 3))*h5
include h5 ann in
theorem image_15_5_0 (f : HomData π 15 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_15_7_0 (f : HomData π 15 7) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^7*(f.v 2) + π^6*(f.v 5) - π^3*(f.v 11) + π^2*(f.v 11) - π*(f.v 1) + (f.v 3) + (f.v 4))*h5
include h5 ann in
theorem image_15_8_0 (f : HomData π 15 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^3)*h0 + (-π^2)*h2 + (-π^8*(f.v 2) + π^7*(f.v 5) - π^4*(f.v 11) + π^3*(f.v 11) - π^2*(f.v 1) + π*(f.v 4) + (f.v 3))*h5
include h5 ann in
theorem image_15_11_0 (f : HomData π 15 11) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^7*(f.v 2) + π^6*(f.v 5) - π^3*(f.v 11) + π^2*(f.v 11) - π*(f.v 1) + (f.v 3) + (f.v 4))*h5
include h5 ann in
theorem image_15_12_0 (f : HomData π 15 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^3)*h0 + (-π^2)*h2 + (-π^8*(f.v 2) + π^7*(f.v 5) - π^4*(f.v 11) + π^3*(f.v 11) - π*(f.v 1) + (f.v 3) + (f.v 4))*h5
include h5 ann in
theorem image_15_17_0 (f : HomData π 15 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^3)*h0 + (-π^2)*h2 + (-π^4*(f.v 11) + π^4*(f.v 3) - π^3*(f.v 0) + π^3*(f.v 11) - π*(f.v 2) + (f.v 4) + (f.v 5))*h5
include h5 ann in
theorem image_16_2_0 (f : HomData π 16 2) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π)*h0 + (-1)*h2 + (-π^6*(f.v 1) - π^6*(f.v 2) + π^5*(f.v 4) + π^5*(f.v 5) - π^2*(f.v 11) + π*(f.v 11) + (f.v 3))*h5
include h5 ann in
theorem image_16_3_0 (f : HomData π 16 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^6*(f.v 4) + π^6*(f.v 5) - π^3*(f.v 11) + π^2*(f.v 11) + (f.v 3))*h5
include h5 ann in
theorem image_16_4_0 (f : HomData π 16 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^3*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_16_5_0 (f : HomData π 16 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 11) + π*(f.v 9))*h5
include h5 ann in
theorem image_16_7_0 (f : HomData π 16 7) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^7*(f.v 2) + π^6*(f.v 5) - π^3*(f.v 11) + π^2*(f.v 11) - π*(f.v 1) + (f.v 3) + (f.v 4))*h5
include h5 ann in
theorem image_16_8_0 (f : HomData π 16 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π^2*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_16_11_0 (f : HomData π 16 11) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h2
  norm_num at h0 h2
  linear_combination (π^2)*h0 + (-π)*h2 + (-π^7*(f.v 2) + π^6*(f.v 5) - π^3*(f.v 11) + π^2*(f.v 11) - π*(f.v 1) + (f.v 3) + (f.v 4))*h5
include h5 ann in
theorem image_16_12_0 (f : HomData π 16 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - π*(f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_16_14_0 (f : HomData π 16 14) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h4 := f.commutes 2 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4
  norm_num at h0 h4
  linear_combination (π^2)*h0 + (-1)*h4 + (-π^7*(f.v 2) + π^5*(f.v 8) - π^4*(f.v 11) + π^2*(f.v 11) + π*(f.v 6) - (f.v 1) + (f.v 7))*h5
include h5 ann in
theorem image_16_15_0 (f : HomData π 16 15) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 11) - (f.v 1) + (f.v 9))*h5
include h5 ann in
theorem image_16_17_0 (f : HomData π 16 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^3*(f.v 0) + π^3*(f.v 11) - π*(f.v 2) + (f.v 9))*h5
include h5 ann in
theorem image_17_2_0 (f : HomData π 17 2) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h4 := f.commutes 2 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4
  norm_num at h0 h4
  linear_combination (π)*h0 + (-1)*h4 + (-π^6*(f.v 1) - π^6*(f.v 2) + π^5*(f.v 7) + π^5*(f.v 8) + π^3*(f.v 9) + π*(f.v 6) - (f.v 9))*h5
include h5 ann in
theorem image_17_3_0 (f : HomData π 17 3) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 1) - π^7*(f.v 2) + π^3*(f.v 9) + (f.v 11))*h5
include h5 ann in
theorem image_17_4_0 (f : HomData π 17 4) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 1) - π^8*(f.v 2) + π^3*(f.v 9) + π*(f.v 11))*h5
include h5 ann in
theorem image_17_4_1 (f : HomData π 17 4) : ρ ((f.v 3))=0 := by
  apply (ann _).mp
  have h2 := f.commutes 1 0
  have h4 := f.commutes 2 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h2 h4
  norm_num at h2 h4
  linear_combination (π^3)*h2 + (-π)*h4 + (-π^8*(f.v 4) - π^8*(f.v 5) + π^6*(f.v 7) + π^6*(f.v 8) + π^3*(f.v 11) - (f.v 11) + (f.v 6))*h5
include h5 ann in
theorem image_17_5_0 (f : HomData π 17 5) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^4)*h0 + (-π^9*(f.v 1) - π^9*(f.v 2) + π^4*(f.v 9) + π^2*(f.v 11))*h5
include h5 ann in
theorem image_17_5_1 (f : HomData π 17 5) : ρ ((f.v 3))=0 := by
  apply (ann _).mp
  have h2 := f.commutes 1 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h2
  norm_num at h2
  linear_combination (π^4)*h2 + (-π^9*(f.v 4) - π^9*(f.v 5) + π^4*(f.v 11) + (f.v 9))*h5
include h5 ann in
theorem image_17_7_0 (f : HomData π 17 7) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^3*(f.v 9) - π*(f.v 1) + (f.v 11))*h5
include h5 ann in
theorem image_17_8_0 (f : HomData π 17 8) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 9) - π^2*(f.v 1) + π*(f.v 11))*h5
include h5 ann in
theorem image_17_8_1 (f : HomData π 17 8) : ρ ((f.v 3))=0 := by
  apply (ann _).mp
  have h2 := f.commutes 1 0
  have h4 := f.commutes 2 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h2 h4
  norm_num at h2 h4
  linear_combination (π^3)*h2 + (-π)*h4 + (-π^8*(f.v 5) + π^6*(f.v 8) + π^3*(f.v 11) - π^2*(f.v 4) - (f.v 11) + (f.v 6) + (f.v 7))*h5
include h5 ann in
theorem image_17_10_0 (f : HomData π 17 10) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^3*(f.v 9) - (f.v 1) + (f.v 11))*h5
include h5 ann in
theorem image_17_11_0 (f : HomData π 17 11) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^3*(f.v 9) - π*(f.v 1) + (f.v 11))*h5
include h5 ann in
theorem image_17_12_0 (f : HomData π 17 12) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 9) - π*(f.v 1) + π*(f.v 11))*h5
include h5 ann in
theorem image_17_13_0 (f : HomData π 17 13) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  have h4 := f.commutes 2 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0 h4
  norm_num at h0 h4
  linear_combination (π)*h0 + (-1)*h4 + (-π^6*(f.v 2) + π^5*(f.v 8) + π^3*(f.v 9) + π*(f.v 6) - (f.v 1) + (f.v 7) - (f.v 9))*h5
include h5 ann in
theorem image_17_14_0 (f : HomData π 17 14) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (-π^7*(f.v 2) + π^3*(f.v 9) - (f.v 1) + (f.v 11))*h5
include h5 ann in
theorem image_17_15_0 (f : HomData π 17 15) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^8*(f.v 2) + π^3*(f.v 9) + π*(f.v 11) - (f.v 1))*h5
include h5 ann in
theorem image_17_16_0 (f : HomData π 17 16) : ρ ((f.v 0))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^2)*h0 + (π^3*(f.v 9) - π*(f.v 2) - (f.v 1) + (f.v 11))*h5
include h5 ann in
theorem image_17_17_0 (f : HomData π 17 17) : ρ ((f.v 1))=0 := by
  apply (ann _).mp
  have h0 := f.commutes 0 0
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h0
  norm_num at h0
  linear_combination (π^3)*h0 + (-π^3*(f.v 0) + π^3*(f.v 9) + π*(f.v 11) - π*(f.v 2))*h5
include h5 ann in
theorem image_17_17_1 (f : HomData π 17 17) : ρ (-(f.v 0) + (f.v 4))=0 := by
  apply (ann _).mp
  have h1 := f.commutes 0 1
  have h2 := f.commutes 1 0
  have h4 := f.commutes 2 0
  have q5 := f.commutes 2 1
  simp only [equation,ambient,source,embedding,ell,src,gen,Matrix.mul_apply,Fin.sum_univ_succ] at h1 h2 h4 q5
  norm_num at h1 h2 h4 q5
  linear_combination (-π)*h1 + (π^3)*h2 + (-π)*h4 + (1)*q5 + (π^4*(f.v 6) - π^3*(f.v 10) + π^3*(f.v 11) - π^3*(f.v 3) - π^3*(f.v 7) + π*(f.v 1) - π*(f.v 5) - π*(f.v 6) + (f.v 10) - (f.v 11) + (f.v 2) + (f.v 7))*h5
end Raw
end UniserialComputations.N5
