import UniformObjects
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

end UniserialComputations.Uniform.Data
