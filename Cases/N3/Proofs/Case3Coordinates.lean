import Case3Data
import UniformQuotient

namespace UniserialComputations.Uniform.Case3
abbrev coordinates : FreeCoordinates Data.objects3 (Fin 5) where
  vertex := ![0,1,2,3,4]
  row := ![0,0,0,0,0]
  valid := by decide
  injective := by decide
  complete := by decide
end UniserialComputations.Uniform.Case3
