import N6ImageData
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
variable (k : Type*) [Field k]
lemma normal_step_20 : ∀ x : Fin 50, let c : Fin 1708 := ⟨x.val+1000,by omega⟩;
  if c.val<47 then normalPath c=[] ∧ normalBlock c=unitBlock ℤ (normalSource c)
  else (normalPrevious c).val<c.val ∧
    normalSource (normalPrevious c)=normalSource c ∧
    normalPath c=normalPath (normalPrevious c)++[normalLast c] ∧
    normalBlock c=arrowMatrix ℤ (normalLast c)*normalBlock (normalPrevious c) := by decide +kernel
end UniserialComputations.N6.Presentation
