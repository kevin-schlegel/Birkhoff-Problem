import Case5Data
import UniformQuotient

namespace UniserialComputations.Uniform.Case5
abbrev coordinates : FreeCoordinates Data.objects5 (Fin 19) where
  vertex := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,17]
  row := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]
  valid := by decide
  injective := by decide
  complete := by decide
end UniserialComputations.Uniform.Case5
