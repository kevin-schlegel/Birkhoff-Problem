import Case4LiftRow0
import Case4LiftRow1
import Case4LiftRow2
import Case4LiftRow3
import Case4LiftRow4
import Case4LiftRow5
import Case4LiftRow6
import Case4LiftRow7
import Case4LiftRow8

noncomputable section
namespace UniserialComputations.Uniform.Case4
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 4 R k π ρ)
include h in
theorem image_surjective (T : N4.End k) :
    ∃ f : Data.objects4.EndRepresentatives π, coordinates.reduce π ρ f = T.val := by
  choose v hv using fun a b => h.residue_surjective (T.val a b)
  refine ⟨liftValues π ρ h v, ?_⟩
  ext a b
  fin_cases a
  · exact lift_row_0 π ρ h T v hv b
  · exact lift_row_1 π ρ h T v hv b
  · exact lift_row_2 π ρ h T v hv b
  · exact lift_row_3 π ρ h T v hv b
  · exact lift_row_4 π ρ h T v hv b
  · exact lift_row_5 π ρ h T v hv b
  · exact lift_row_6 π ρ h T v hv b
  · exact lift_row_7 π ρ h T v hv b
  · exact lift_row_8 π ρ h T v hv b
include h in
theorem image_eq : coordinates.imageAlgebra π ρ h = N4.endAlgebra k := by
  ext M
  constructor
  · rintro ⟨f,rfl⟩
    exact image_mem π ρ h f
  · intro H
    exact image_surjective π ρ h ⟨M,H⟩
end UniserialComputations.Uniform.Case4
