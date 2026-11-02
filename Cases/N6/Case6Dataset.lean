import Case6Quiver
import Case6FreeCoordinates
import UniformDataset
namespace UniserialComputations.Uniform.Data
abbrev case6 : Dataset where
  objects := objects6
  Slot := Data.Slot6
  slotFintype := inferInstance
  slotDecidableEq := inferInstance
  coordinates := Case6.coordinates
  quiver := quiver6
  arrowMatrix := arrows6
  dimension := 1708
end UniserialComputations.Uniform.Data
