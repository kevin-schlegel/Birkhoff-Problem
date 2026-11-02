import Case2Data
import UniformPaths

namespace UniserialComputations.Uniform.Data
abbrev quiver2 : QuiverData objects2.vertices where
  arrows := 2
  source := ![1,2]
  target := ![0,1]
  relations := []
def arrows2 (a : Fin quiver2.arrows) : Matrix (Fin 3) (Fin 3) Int :=
  Matrix.single (quiver2.target a) (quiver2.source a) 1
end UniserialComputations.Uniform.Data
