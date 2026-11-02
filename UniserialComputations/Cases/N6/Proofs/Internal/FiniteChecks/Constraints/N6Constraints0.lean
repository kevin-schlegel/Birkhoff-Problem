import N6Matrix
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem constraint_0_46_0_0 (f : HomData π 0 46) : ρ ((f.M 0 0))=0 := by
  apply (ann _).mp
  have h20 := f.commutes 0 0
  simp only [ambientLength,sourceLength,embedding,Matrix.mul_apply,Fin.sum_univ_succ] at h20
  norm_num at h20
  linear_combination (π^5)*h20 + ((f.U 0 0))*h6
end UniserialComputations.N6
