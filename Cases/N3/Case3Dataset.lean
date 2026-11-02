import Case3Quiver
import Case3Coordinates
import UniformDataset
namespace UniserialComputations.Uniform.Data
abbrev case3 : Dataset where
  objects := objects3
  Slot := Fin 5
  slotFintype := inferInstance
  slotDecidableEq := inferInstance
  coordinates := Case3.coordinates
  quiver := quiver3
  arrowMatrix := arrows3
  dimension := 15
end UniserialComputations.Uniform.Data
