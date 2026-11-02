import Case5Data
import UniformPaths

namespace UniserialComputations.Uniform.Data
abbrev quiver5 : QuiverData objects5.vertices where
  arrows := 23
  source := ![0,1,2,3,4,6,7,8,9,10,11,11,12,13,13,14,14,15,16,16,17,17,17]
  target := ![1,6,7,17,5,9,11,4,17,16,3,12,17,2,16,11,15,12,7,14,8,10,13]
  relations := [
    [(1,[3,21])], -- relation 0
    [(1,[3,22])], -- relation 1
    [(1,[8,20])], -- relation 2
    [(1,[12,21])], -- relation 3
    [(1,[12,22])], -- relation 4
    [(1,[10,3]),(-1,[11,12])], -- relation 5
    [(1,[13,2]),(-1,[14,18])], -- relation 6
    [(1,[15,11]),(-1,[16,17])], -- relation 7
    [(1,[18,6]),(-1,[19,15])], -- relation 8
    [(1,[21,9]),(-1,[22,14])] -- relation 9
  ]
abbrev arrowRow5 : Fin 23 → Fin 19 := ![1,6,7,18,5,9,11,4,17,16,3,12,18,2,16,11,15,12,7,14,8,10,13]
abbrev arrowCol5 : Fin 23 → Fin 19 := ![0,1,2,3,4,6,7,8,9,10,11,11,12,13,13,14,14,15,16,16,18,17,17]
def arrows5 (a : Fin 23) : Matrix (Fin 19) (Fin 19) Int :=
  Matrix.single (arrowRow5 a) (arrowCol5 a) 1
end UniserialComputations.Uniform.Data
