import Case4Data
import UniformPaths

namespace UniserialComputations.Uniform.Data
abbrev quiver4 : QuiverData objects4.vertices where
  arrows := 9
  source := ![1,2,3,4,5,5,6,7,8]
  target := ![0,1,2,2,3,4,5,6,7]
  relations := [
    [(1,[4,2]),(-1,[5,3])] -- relation 0
  ]
def arrows4 (a : Fin quiver4.arrows) : Matrix (Fin 9) (Fin 9) Int :=
  Matrix.single (quiver4.target a) (quiver4.source a) 1
end UniserialComputations.Uniform.Data
