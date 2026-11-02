import Case2Quiver
import UniformMatrixPaths
import Final

noncomputable section
namespace UniserialComputations.Uniform.Case2.Presentation
open QuiverData
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (k : Type*) [Field k]
abbrev Allowed (i j : Fin 3) : Prop := i ≤ j
lemma single_mem (i j : Fin 3) (h : Allowed i j) : Matrix.single i j (1:k) ∈ N2.endAlgebra k := by
  intro a b hab
  simp only [Matrix.single_apply]
  split_ifs with hh
  · obtain ⟨rfl,rfl⟩ := hh
    omega
  · rfl
def representation : Data.quiver2.Representation k (N2.End k) :=
  Data.quiver2.matrixRepresentation k (N2.endAlgebra k)
    (fun i => single_mem k i i (by rfl))
    (fun b => single_mem k _ _ (by fin_cases b <;> decide))
abbrev pathMap := (representation k).pathMap

lemma relations_zero (z : Fin Data.quiver2.relations.length) :
    pathMap k (Data.quiver2.polynomial (Data.quiver2.arrow k) Data.quiver2.relations[z])=0 := by
  exact Fin.elim0 z
def evaluate : Data.quiver2.Presented k →ₐ[k] N2.End k :=
  (representation k).evaluate (relations_zero k)
abbrev normalSource : Fin 6 → Fin 3 := ![0,1,2,1,2,2]
abbrev normalTarget : Fin 6 → Fin 3 := ![0,0,0,1,1,2]
abbrev normalPath : Fin 6 → List (Fin Data.quiver2.arrows) := ![[],[0],[1,0],[],[1],[]]
abbrev normalIndex : Fin 3 → Fin 3 → Fin 6 := ![![0,1,2],![0,3,4],![0,0,5]]
theorem normalIndex_spec : ∀ i j, Allowed i j →
    normalTarget (normalIndex i j)=i ∧ normalSource (normalIndex i j)=j := by decide
theorem normal_endpoints : ∀ c, Data.quiver2.walkEnd (normalSource c) (normalPath c)=some (normalTarget c) := by decide
def normal (c : Fin 6) : Data.quiver2.Presented k := Data.quiver2.walk k (normalSource c) (normalPath c)
def pathNormal (c : Fin 6) : Data.quiver2.PathAlgebra k :=
  Data.quiver2.word (Data.quiver2.arrow k) (normalPath c) * Data.quiver2.vertex k (normalSource c)
lemma path_image (c : Fin 6) : (pathMap k (pathNormal k c)).val = Matrix.single (normalTarget c) (normalSource c) 1 := by
  rw [pathNormal,Representation.pathMap_walk]
  fin_cases c
  all_goals simp [word,representation,matrixRepresentation,Data.quiver2,normalPath,normalSource,normalTarget]

lemma vertex_mem (i : Fin 3) : Data.quiver2.e k i ∈ normalSpan Data.quiver2 k (normal k) := by
  have H : Data.quiver2.e k i = normal k (normalIndex i i) := by
    fin_cases i <;> simp [normal,normalIndex,normalSource,normalPath,walk,word]
  rw [H]
  exact normal_mem (normal k) _
lemma vertex_span (i : Fin 3) (c : Fin 6) :
    Data.quiver2.e k i * normal k c ∈ normalSpan Data.quiver2 k (normal k) := by
  rw [normal,Data.quiver2.vertex_walk k i _ _ _ (normal_endpoints c)]
  split_ifs
  · exact normal_mem (normal k) c
  · exact Submodule.zero_mem _
end UniserialComputations.Uniform.Case2.Presentation
