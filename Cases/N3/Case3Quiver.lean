import Case3Data
import UniformPaths

namespace UniserialComputations.Uniform.Data
abbrev quiver3 : QuiverData objects3.vertices where
  arrows := 4
  source := ![1,2,3,4]
  target := ![0,1,2,3]
  relations := []
def arrows3 (a : Fin quiver3.arrows) : Matrix (Fin 5) (Fin 5) Int :=
  Matrix.single (quiver3.target a) (quiver3.source a) 1
end UniserialComputations.Uniform.Data
