import Case5RealizationBase
noncomputable section
namespace UniserialComputations.Uniform.Case5
set_option maxHeartbeats 50000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 5 R k π ρ)
include h in
theorem lift_row_16 (T : N5.End k) (v : Matrix (Fin 19) (Fin 19) R)
    (hv : ∀ a b, ρ (v a b) = T.val a b) :
    ∀ b, coordinates.reduce π ρ (liftValues π ρ h v) 16 b = T.val 16 b := by
  intro b
  fin_cases b
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_16_0_0_0, h.residue_pi, hv]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_16_1_0_0, h.residue_pi, hv]
  · have hz := T.property.1 16 2 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · have hz := T.property.1 16 3 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · have hz := T.property.1 16 4 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · have hz := T.property.1 16 5 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_16_6_0_0, h.residue_pi, hv]
  · have hz := T.property.1 16 7 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · have hz := T.property.1 16 8 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_16_9_0_0, h.residue_pi, hv]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_16_10_0_0, h.residue_pi, hv]
  · have hz := T.property.1 16 11 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · have hz := T.property.1 16 12 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_16_13_0_0, h.residue_pi, hv]
  · have hz := T.property.1 16 14 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · have hz := T.property.1 16 15 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_16_16_0_0, h.residue_pi, hv]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_16_17_0_0, h.residue_pi, hv]
  · have hz := T.property.1 16 18 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_16_17_0_0, h.residue_pi, hv, hz]
end UniserialComputations.Uniform.Case5
