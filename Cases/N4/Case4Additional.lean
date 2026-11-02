import UniformLocal
namespace UniserialComputations.Uniform.Data
/-- Additional objects for the locality computation, in database order. -/
abbrev additional4 : ObjectFamily where
  length := 4
  vertices := 1
  ambientSlots := 2
  sourceSlots := 2
  labels := !["26"]
  ambientLength := ![
    ![4,2] -- 0: 26
  ]
  sourceLength := ![
    ![3,1] -- 0: 26
  ]
  entry := ![
    ![![(1,1),(0,0)],![(1,0),(1,1)]] -- 0: 26
  ]
  ambientBound := by decide
  sourceBound := by decide

abbrev additionalCoordinates4 (i : Fin additional4.vertices) :
    FreeCoordinates (additional4.singleObject i) (Fin 1) where
  vertex := fun _ => 0
  row := fun _ => 0
  valid := by fin_cases i <;> decide
  injective := fun _ _ _ => Subsingleton.elim _ _
  complete := by fin_cases i <;> decide
end UniserialComputations.Uniform.Data
