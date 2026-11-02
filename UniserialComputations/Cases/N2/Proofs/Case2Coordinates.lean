import Case2Data
import UniformQuotient

namespace UniserialComputations.Uniform.Case2
abbrev coordinates : FreeCoordinates Data.objects2 (Fin 3) where
  vertex := ![0,1,2]
  row := ![0,0,0]
  valid := by decide
  injective := by decide
  complete := by decide
end UniserialComputations.Uniform.Case2
