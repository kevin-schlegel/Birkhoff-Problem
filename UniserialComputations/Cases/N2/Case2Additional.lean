import UniformLocal
namespace UniserialComputations.Uniform.Data
/-- Additional objects for the locality computation, in database order. -/
abbrev additional2 : ObjectFamily where
  length := 2
  vertices := 0
  ambientSlots := 1
  sourceSlots := 1
  labels := Fin.elim0
  ambientLength := Fin.elim0
  sourceLength := Fin.elim0
  entry := Fin.elim0
  ambientBound := by decide
  sourceBound := by decide

abbrev additionalCoordinates2 (i : Fin additional2.vertices) :
    FreeCoordinates (additional2.singleObject i) (Fin 1) where
  vertex := fun _ => 0
  row := fun _ => 0
  valid := by exact Fin.elim0 i
  injective := fun _ _ _ => Subsingleton.elim _ _
  complete := by exact Fin.elim0 i
end UniserialComputations.Uniform.Data
