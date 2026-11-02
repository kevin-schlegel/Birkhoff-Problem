import N5Computations
noncomputable section
namespace UniserialComputations.N5

def oldObjects : List DBObject := N4.oldObjects ++ N4.newObjects ++ N4.nextStartingObjects
theorem old_count : oldObjects.length=20 := by decide
theorem escaping_count : escapingTranslateIDs.length=16 := by decide
theorem translation_target_list :
    ((escapingTranslateIDs.map Prod.snd)++[15,20]).toFinset=vertexIDs.toFinset := by decide
theorem c3_id_list : c3Objects.map DBObject.id=[33,35,38,40,41,42,44,45,46,47,48,49] := by decide
/-- The correction supplied with the n=5 computation is part of the checked data. -/
theorem corrected_42 :
    objects.find? (fun o => o.id=42) = some ⟨42,[4,2],[5,3,1],[[some 1,some 0,none],[none,some 1,some 0]]⟩ := by decide

variable (k : Type*) [Field k]
def dualMultiply (x y : k × k) : k × k := (x.1*y.1,x.2*y.1+x.1*y.2)
def dualMatrix (x : k × k) : Matrix (Fin 2) (Fin 2) k := !![x.1,0;x.2,x.1]
theorem dualMatrix_multiply (x y : k × k) :
    dualMatrix k (dualMultiply k x y)=dualMatrix k x*dualMatrix k y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dualMatrix,dualMultiply,Matrix.mul_apply,Fin.sum_univ_succ]
theorem dual_local_certificate (x : k × k) : ∃ y : k × k,
    (dualMultiply k x y=(1,0) ∧ dualMultiply k y x=(1,0)) ∨
    (dualMultiply k ((1,0)-x) y=(1,0) ∧ dualMultiply k y ((1,0)-x)=(1,0)) := by
  by_cases h : x.1=0
  · refine ⟨(1,x.2),Or.inr ?_⟩
    simp [dualMultiply,h]
  · refine ⟨(x.1⁻¹,-x.2*x.1⁻¹*x.1⁻¹),Or.inl ?_⟩
    constructor <;> apply Prod.ext
    all_goals simp only [dualMultiply,Prod.fst,Prod.snd]
    all_goals field_simp
    all_goals simp_all
    all_goals ring
end UniserialComputations.N5
