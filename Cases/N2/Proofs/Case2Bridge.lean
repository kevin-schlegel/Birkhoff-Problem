import Case2LiftRow0
import Case2LiftRow1
import Case2LiftRow2

noncomputable section
namespace UniserialComputations.Uniform.Case2
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 2 R k π ρ)
include h in
theorem image_surjective (T : N2.End k) :
    ∃ f : Data.objects2.EndRepresentatives π, coordinates.reduce π ρ f = T.val := by
  choose v hv using fun a b => h.residue_surjective (T.val a b)
  refine ⟨liftValues π ρ h v, ?_⟩
  ext a b
  fin_cases a
  · exact lift_row_0 π ρ h T v hv b
  · exact lift_row_1 π ρ h T v hv b
  · exact lift_row_2 π ρ h T v hv b
include h in
theorem image_eq : coordinates.imageAlgebra π ρ h = N2.endAlgebra k := by
  ext M
  constructor
  · rintro ⟨f,rfl⟩
    exact image_mem π ρ h f
  · intro H
    exact image_surjective π ρ h ⟨M,H⟩
end UniserialComputations.Uniform.Case2
