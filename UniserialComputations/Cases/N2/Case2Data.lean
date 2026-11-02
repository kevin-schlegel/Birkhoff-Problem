import UniformObjects

namespace UniserialComputations.Uniform.Data

/-- Object family for length 2. Labels identify the dataset entries. -/
abbrev objects2 : ObjectFamily where
  length := 2
  vertices := 3
  ambientSlots := 1
  sourceSlots := 1
  labels := !["5","4","3"]
  ambientLength := ![
    ![2], -- 0: 5
    ![2], -- 1: 4
    ![2] -- 2: 3
  ]
  sourceLength := ![
    ![2], -- 0: 5
    ![1], -- 1: 4
    ![0] -- 2: 3
  ]
  entry := ![
    ![![(1,0)]], -- 0: 5
    ![![(1,1)]], -- 1: 4
    ![![(0,0)]] -- 2: 3
  ]
  ambientBound := by decide
  sourceBound := by decide

end UniserialComputations.Uniform.Data
