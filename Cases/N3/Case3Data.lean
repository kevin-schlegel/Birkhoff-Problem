import UniformObjects

namespace UniserialComputations.Uniform.Data

/-- Object family for length 3. Labels identify the dataset entries. -/
abbrev objects3 : ObjectFamily where
  length := 3
  vertices := 5
  ambientSlots := 2
  sourceSlots := 1
  labels := !["9","8","21","7","6"]
  ambientLength := ![
    ![3,0], -- 0: 9
    ![3,0], -- 1: 8
    ![3,1], -- 2: 21
    ![3,0], -- 3: 7
    ![3,0] -- 4: 6
  ]
  sourceLength := ![
    ![3], -- 0: 9
    ![2], -- 1: 8
    ![2], -- 2: 21
    ![1], -- 3: 7
    ![0] -- 4: 6
  ]
  entry := ![
    ![![(1,0)],![(0,0)]], -- 0: 9
    ![![(1,1)],![(0,0)]], -- 1: 8
    ![![(1,1)],![(1,0)]], -- 2: 21
    ![![(1,2)],![(0,0)]], -- 3: 7
    ![![(0,0)],![(0,0)]] -- 4: 6
  ]
  ambientBound := by decide
  sourceBound := by decide

end UniserialComputations.Uniform.Data
