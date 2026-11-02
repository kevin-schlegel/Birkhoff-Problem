import Case6Quiver
import N6Data
import UniformQuotient
namespace UniserialComputations.Uniform.Case6
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000
abbrev freeSlot : Fin 47 → Fin 2 → Fin 4 := ![![0,0],![0,0],![1,0],![0,0],![1,0],![1,0],![0,0],![1,0],![1,0],![1,0],![0,0],![1,0],![1,0],![1,0],![1,0],![1,0],![1,0],![1,0],![1,2],![1,0],![2,0],![1,0],![1,0],![1,0],![1,2],![1,0],![1,2],![2,0],![1,0],![2,0],![1,2],![1,2],![2,3],![1,0],![2,0],![2,0],![2,0],![1,2],![2,3],![2,3],![2,3],![2,3],![2,3],![2,3],![2,3],![0,0],![0,0]]
abbrev coordinates : FreeCoordinates Data.objects6 Data.Slot6 where
  vertex a := a.1
  row a := freeSlot a.1 (Data.part6 a)
  valid a := N6.free_slot_valid _ _ a.2.isLt
  injective := by
    rintro ⟨i,a⟩ ⟨j,b⟩ H
    have hij : i = j := congrArg Prod.fst H
    cases hij
    have hr := congrArg Prod.snd H
    have hab := N6.free_slot_injective i (Data.part6 ⟨i,a⟩) (Data.part6 ⟨i,b⟩) a.isLt b.isLt hr
    have hab' : a = b := Fin.ext (congrArg (fun x : Fin 2 => x.val) hab)
    cases hab'
    rfl
  complete := by
    intro i r hr
    obtain ⟨a,ha,har⟩ := (N6.free_slot_complete i r).mp hr
    exact ⟨⟨i,⟨a.val,ha⟩⟩,rfl,har⟩
end UniserialComputations.Uniform.Case6
