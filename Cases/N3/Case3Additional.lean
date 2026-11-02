import UniformLocal
namespace UniserialComputations.Uniform.Data
/-- Additional objects for the locality computation, in database order. -/
abbrev additional3 : ObjectFamily where
  length := 3
  vertices := 0
  ambientSlots := 1
  sourceSlots := 1
  labels := Fin.elim0
  ambientLength := Fin.elim0
  sourceLength := Fin.elim0
  entry := Fin.elim0
  ambientBound := by decide
  sourceBound := by decide

abbrev additionalCoordinates3 (i : Fin additional3.vertices) :
    FreeCoordinates (additional3.singleObject i) (Fin 1) where
  vertex := fun _ => 0
  row := fun _ => 0
  valid := by exact Fin.elim0 i
  injective := fun _ _ _ => Subsingleton.elim _ _
  complete := by exact Fin.elim0 i
end UniserialComputations.Uniform.Data
