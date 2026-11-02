import N6AllLifts
import N6HomCompleteness
import N6HomOperations
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r,π^5*r=0 ↔ ρ r=0) (surj : Function.Surjective ρ)
include h6 ann surj
theorem realizes_param (i j : Fin 47) (x : Fin 3 → k) :
    ∃ f : HomData π i j, reduceHom π ρ f=param k (homKind i j) x := by
  choose y hy using fun b => surj (x b)
  refine ⟨homSum3 π (fun b => homScale π (y b) (basisLift π h6 i j b)),?_⟩
  rw [reduce_homSum3]
  unfold param
  apply Finset.sum_congr rfl
  intro b _
  rw [reduce_homScale,basisLift_reduces π ρ h6 ann,hy]
theorem realizes_normal (i j : Fin 47) (A : Block k) (hA : Normal k (homKind i j) A) :
    ∃ f : HomData π i j, reduceHom π ρ f=A := by
  obtain ⟨f,hf⟩ := realizes_param π ρ h6 ann surj i j (coords k (homKind i j) A)
  exact ⟨f,hf.trans hA⟩
/-- Complete quotient Hom description, with the residue map explicitly surjective. -/
theorem quotient_hom_description (i j : Fin 47) (A : Block k) :
    (∃ f : HomData π i j, reduceHom π ρ f=A) ↔ Normal k (homKind i j) A := by
  constructor
  · rintro ⟨f,rfl⟩
    exact image_normal π ρ h6 ann i j f
  · exact realizes_normal π ρ h6 ann surj i j A
end UniserialComputations.N6
