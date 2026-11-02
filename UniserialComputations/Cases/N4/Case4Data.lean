import UniformObjects

namespace UniserialComputations.Uniform.Data

/-- Object family for length 4. Labels identify the dataset entries. -/
abbrev objects4 : ObjectFamily where
  length := 4
  vertices := 9
  ambientSlots := 2
  sourceSlots := 1
  labels := !["14","13","23","12","25","24","22","11","10"]
  ambientLength := ![
    ![4,0], -- 0: 14
    ![4,0], -- 1: 13
    ![4,1], -- 2: 23
    ![4,0], -- 3: 12
    ![4,2], -- 4: 25
    ![4,2], -- 5: 24
    ![4,1], -- 6: 22
    ![4,0], -- 7: 11
    ![4,0] -- 8: 10
  ]
  sourceLength := ![
    ![4], -- 0: 14
    ![3], -- 1: 13
    ![3], -- 2: 23
    ![2], -- 3: 12
    ![3], -- 4: 25
    ![2], -- 5: 24
    ![2], -- 6: 22
    ![1], -- 7: 11
    ![0] -- 8: 10
  ]
  entry := ![
    ![![(1,0)],![(1,0)]], -- 0: 14
    ![![(1,1)],![(1,0)]], -- 1: 13
    ![![(1,1)],![(1,0)]], -- 2: 23
    ![![(1,2)],![(1,0)]], -- 3: 12
    ![![(1,1)],![(1,0)]], -- 4: 25
    ![![(1,2)],![(1,1)]], -- 5: 24
    ![![(1,2)],![(1,0)]], -- 6: 22
    ![![(1,3)],![(1,0)]], -- 7: 11
    ![![(1,4)],![(1,0)]] -- 8: 10
  ]
  ambientBound := by decide
  sourceBound := by decide

end UniserialComputations.Uniform.Data
