import UniformObjects
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

end UniserialComputations.Uniform.Data
