import Case2Quiver
import Case2Coordinates
import UniformDataset
namespace UniserialComputations.Uniform.Data
abbrev case2 : Dataset where
  objects := objects2
  Slot := Fin 3
  slotFintype := inferInstance
  slotDecidableEq := inferInstance
  coordinates := Case2.coordinates
  quiver := quiver2
  arrowMatrix := arrows2
  dimension := 6
end UniserialComputations.Uniform.Data
