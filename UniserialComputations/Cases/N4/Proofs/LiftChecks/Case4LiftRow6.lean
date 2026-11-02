import Case4RealizationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4
set_option maxHeartbeats 50000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 4 R k π ρ)
include h in
theorem lift_row_6 (T : N4.End k) (v : Matrix (Fin 9) (Fin 9) R)
    (hv : ∀ a b, ρ (v a b) = T.val a b) :
    ∀ b, coordinates.reduce π ρ (liftValues π ρ h v) 6 b = T.val 6 b := by
  intro b
  fin_cases b
  · have hz := T.property 6 0 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · have hz := T.property 6 1 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · have hz := T.property 6 2 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · have hz := T.property 6 3 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · have hz := T.property 6 4 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · have hz := T.property 6 5 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_6_6_0_0, h.residue_pi, hv]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_6_7_0_0, h.residue_pi, hv]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_6_8_0_0, h.residue_pi, hv]
end UniserialComputations.Uniform.Case4
