import Case5LiftRow0
import Case5LiftRow1
import Case5LiftRow2
import Case5LiftRow3
import Case5LiftRow4
import Case5LiftRow5
import Case5LiftRow6
import Case5LiftRow7
import Case5LiftRow8
import Case5LiftRow9
import Case5LiftRow10
import Case5LiftRow11
import Case5LiftRow12
import Case5LiftRow13
import Case5LiftRow14
import Case5LiftRow15
import Case5LiftRow16
import Case5LiftRow17
import Case5LiftRow18

noncomputable section
namespace UniserialComputations.Uniform.Case5
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 5 R k π ρ)
include h in
theorem image_surjective (T : N5.End k) :
    ∃ f : Data.objects5.EndRepresentatives π, coordinates.reduce π ρ f = T.val := by
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
  · exact lift_row_9 π ρ h T v hv b
  · exact lift_row_10 π ρ h T v hv b
  · exact lift_row_11 π ρ h T v hv b
  · exact lift_row_12 π ρ h T v hv b
  · exact lift_row_13 π ρ h T v hv b
  · exact lift_row_14 π ρ h T v hv b
  · exact lift_row_15 π ρ h T v hv b
  · exact lift_row_16 π ρ h T v hv b
  · exact lift_row_17 π ρ h T v hv b
  · exact lift_row_18 π ρ h T v hv b
include h in
theorem image_eq : coordinates.imageAlgebra π ρ h = N5.endAlgebra k := by
  ext M
  constructor
  · rintro ⟨f,rfl⟩
    exact image_mem π ρ h f
  · intro H
    exact image_surjective π ρ h ⟨M,H⟩
end UniserialComputations.Uniform.Case5
