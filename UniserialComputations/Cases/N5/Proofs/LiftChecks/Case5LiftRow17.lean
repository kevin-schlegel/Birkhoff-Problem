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
theorem lift_row_17 (T : N5.End k) (v : Matrix (Fin 19) (Fin 19) R)
    (hv : ∀ a b, ρ (v a b) = T.val a b) :
    ∀ b, coordinates.reduce π ρ (liftValues π ρ h v) 17 b = T.val 17 b := by
  intro b
  fin_cases b
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_0_0_0, lift_17_0_1_0, h.residue_pi, hv]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_1_0_0, lift_17_1_1_0, h.residue_pi, hv]
  · have hz := T.property.1 17 2 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_2_1_0, h.residue_pi, hv, hz]
  · have hz := T.property.1 17 3 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_3_1_0, h.residue_pi, hv, hz]
  · have hz := T.property.1 17 4 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · have hz := T.property.1 17 5 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_6_0_0, lift_17_6_1_0, h.residue_pi, hv]
  · have hz := T.property.1 17 7 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_7_1_0, h.residue_pi, hv, hz]
  · have hz := T.property.1 17 8 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, h.residue_pi, hv, hz]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_9_0_0, lift_17_9_1_0, h.residue_pi, hv]
  · have hz := T.property.1 17 10 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_10_1_0, h.residue_pi, hv, hz]
  · have hz := T.property.1 17 11 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_11_1_0, h.residue_pi, hv, hz]
  · have hz := T.property.1 17 12 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_12_1_0, h.residue_pi, hv, hz]
  · have hz := T.property.1 17 13 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_13_1_0, h.residue_pi, hv, hz]
  · have hz := T.property.1 17 14 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_14_1_0, h.residue_pi, hv, hz]
  · have hz := T.property.1 17 15 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_15_1_0, h.residue_pi, hv, hz]
  · have hz := T.property.1 17 16 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_16_1_0, h.residue_pi, hv, hz]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_17_0_0, lift_17_17_1_0, h.residue_pi, hv]
  · have hz := T.property.1 17 18 (by decide)
    simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_17_17_0_0, lift_17_17_1_0, h.residue_pi, hv, hz]
end UniserialComputations.Uniform.Case5
