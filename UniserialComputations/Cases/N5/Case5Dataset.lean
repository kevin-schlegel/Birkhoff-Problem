import Case5Quiver
import Case5Coordinates
import UniformDataset
namespace UniserialComputations.Uniform.Data
abbrev case5 : Dataset where
  objects := objects5
  Slot := Fin 19
  slotFintype := inferInstance
  slotDecidableEq := inferInstance
  coordinates := Case5.coordinates
  quiver := quiver5
  arrowMatrix := arrows5
  dimension := 179
end UniserialComputations.Uniform.Data
