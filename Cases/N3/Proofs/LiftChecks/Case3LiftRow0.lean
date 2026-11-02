import Case3RealizationBase
noncomputable section
namespace UniserialComputations.Uniform.Case3
set_option maxHeartbeats 50000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 3 R k π ρ)
include h in
theorem lift_row_0 (T : N3.End k) (v : Matrix (Fin 5) (Fin 5) R)
    (hv : ∀ a b, ρ (v a b) = T.val a b) :
    ∀ b, coordinates.reduce π ρ (liftValues π ρ h v) 0 b = T.val 0 b := by
  intro b
  fin_cases b
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_0_0_0_0, h.residue_pi, hv]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_0_1_0_0, h.residue_pi, hv]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_0_2_0_0, h.residue_pi, hv]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_0_3_0_0, h.residue_pi, hv]
  · simp [Fin.cases, Fin.induction, Fin.induction.go, FreeCoordinates.reduce, coordinates, liftValues, ObjectFamily.Hom.add, ObjectFamily.Hom.scale, ObjectFamily.Hom.zero, lift_0_4_0_0, h.residue_pi, hv]
end UniserialComputations.Uniform.Case3
