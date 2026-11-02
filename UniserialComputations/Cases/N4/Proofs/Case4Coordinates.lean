import Case4Data
import UniformQuotient

namespace UniserialComputations.Uniform.Case4
abbrev coordinates : FreeCoordinates Data.objects4 (Fin 9) where
  vertex := ![0,1,2,3,4,5,6,7,8]
  row := ![0,0,0,0,0,0,0,0,0]
  valid := by decide
  injective := by decide
  complete := by decide
end UniserialComputations.Uniform.Case4
