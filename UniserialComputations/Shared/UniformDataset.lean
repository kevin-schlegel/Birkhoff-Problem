import UniformQuotient
import UniformPaths

namespace UniserialComputations.Uniform

/-- All finite inputs for one C2 computation. No mathematical conclusion is
included among these fields. -/
structure Dataset where
  objects : ObjectFamily
  Slot : Type
  slotFintype : Fintype Slot
  slotDecidableEq : DecidableEq Slot
  coordinates : FreeCoordinates objects Slot
  quiver : QuiverData objects.vertices
  arrowMatrix : Fin quiver.arrows → Matrix Slot Slot Int
  dimension : Nat

attribute [instance] Dataset.slotFintype Dataset.slotDecidableEq

namespace Dataset
variable (D : Dataset) (k : Type*) [Field k]
abbrev PathAlgebra := D.quiver.PathAlgebra k
abbrev Presented := D.quiver.Presented k
def vertexMatrix (i : Fin D.objects.vertices) : Matrix D.Slot D.Slot k :=
  Matrix.diagonal (fun a => if D.coordinates.vertex a = i then 1 else 0)
def arrowValue (a : Fin D.quiver.arrows) : Matrix D.Slot D.Slot k :=
  (D.arrowMatrix a).map (Int.castRingHom k)
abbrev End {R : Type*} [CommRing R] (π : R) (ρ : R →+* k)
    (h : RingParameters D.objects.length R k π ρ) := EndAlgebra D.coordinates π ρ h
end Dataset

end UniserialComputations.Uniform
