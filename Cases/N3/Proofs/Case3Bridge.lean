import Case3LiftRow0
import Case3LiftRow1
import Case3LiftRow2
import Case3LiftRow3
import Case3LiftRow4

noncomputable section
namespace UniserialComputations.Uniform.Case3
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 3 R k π ρ)
include h in
theorem image_surjective (T : N3.End k) :
    ∃ f : Data.objects3.EndRepresentatives π, coordinates.reduce π ρ f = T.val := by
  choose v hv using fun a b => h.residue_surjective (T.val a b)
  refine ⟨liftValues π ρ h v, ?_⟩
  ext a b
  fin_cases a
  · exact lift_row_0 π ρ h T v hv b
  · exact lift_row_1 π ρ h T v hv b
  · exact lift_row_2 π ρ h T v hv b
  · exact lift_row_3 π ρ h T v hv b
  · exact lift_row_4 π ρ h T v hv b
include h in
theorem image_eq : coordinates.imageAlgebra π ρ h = Chain.endAlgebra k 5 := by
  ext M
  constructor
  · rintro ⟨f,rfl⟩
    exact image_mem π ρ h f
  · intro H
    exact image_surjective π ρ h ⟨M,H⟩
end UniserialComputations.Uniform.Case3
