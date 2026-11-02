import Case4Quiver
import Case4Coordinates
import UniformDataset
namespace UniserialComputations.Uniform.Data
abbrev case4 : Dataset where
  objects := objects4
  Slot := Fin 9
  slotFintype := inferInstance
  slotDecidableEq := inferInstance
  coordinates := Case4.coordinates
  quiver := quiver4
  arrowMatrix := arrows4
  dimension := 44
end UniserialComputations.Uniform.Data
