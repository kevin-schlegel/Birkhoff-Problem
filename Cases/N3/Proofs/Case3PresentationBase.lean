import Case3Quiver
import UniformMatrixPaths
import Final

noncomputable section
namespace UniserialComputations.Uniform.Case3.Presentation
open QuiverData
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (k : Type*) [Field k]
abbrev Allowed (i j : Fin 5) : Prop := i ≤ j
lemma single_mem (i j : Fin 5) (h : Allowed i j) : Matrix.single i j (1:k) ∈ Chain.endAlgebra k 5 := by
  intro a b hab
  simp only [Matrix.single_apply]
  split_ifs with hh
  · obtain ⟨rfl,rfl⟩ := hh
    omega
  · rfl
def representation : Data.quiver3.Representation k (N3.End k) :=
  Data.quiver3.matrixRepresentation k (Chain.endAlgebra k 5)
    (fun i => single_mem k i i (by rfl))
    (fun b => single_mem k _ _ (by fin_cases b <;> decide))
abbrev pathMap := (representation k).pathMap

lemma relations_zero (z : Fin Data.quiver3.relations.length) :
    pathMap k (Data.quiver3.polynomial (Data.quiver3.arrow k) Data.quiver3.relations[z])=0 := by
  exact Fin.elim0 z
def evaluate : Data.quiver3.Presented k →ₐ[k] N3.End k :=
  (representation k).evaluate (relations_zero k)
abbrev normalSource : Fin 15 → Fin 5 := ![0,1,2,3,4,1,2,3,4,2,3,4,3,4,4]
abbrev normalTarget : Fin 15 → Fin 5 := ![0,0,0,0,0,1,1,1,1,2,2,2,3,3,4]
abbrev normalPath : Fin 15 → List (Fin Data.quiver3.arrows) := ![[],[0],[1,0],[2,1,0],[3,2,1,0],[],[1],[2,1],[3,2,1],[],[2],[3,2],[],[3],[]]
abbrev normalIndex : Fin 5 → Fin 5 → Fin 15 := ![![0,1,2,3,4],![0,5,6,7,8],![0,0,9,10,11],![0,0,0,12,13],![0,0,0,0,14]]
theorem normalIndex_spec : ∀ i j, Allowed i j →
    normalTarget (normalIndex i j)=i ∧ normalSource (normalIndex i j)=j := by decide
theorem normal_endpoints : ∀ c, Data.quiver3.walkEnd (normalSource c) (normalPath c)=some (normalTarget c) := by decide
def normal (c : Fin 15) : Data.quiver3.Presented k := Data.quiver3.walk k (normalSource c) (normalPath c)
def pathNormal (c : Fin 15) : Data.quiver3.PathAlgebra k :=
  Data.quiver3.word (Data.quiver3.arrow k) (normalPath c) * Data.quiver3.vertex k (normalSource c)
lemma path_image (c : Fin 15) : (pathMap k (pathNormal k c)).val = Matrix.single (normalTarget c) (normalSource c) 1 := by
  rw [pathNormal,Representation.pathMap_walk]
  fin_cases c
  all_goals simp [word,representation,matrixRepresentation,Data.quiver3,normalPath,normalSource,normalTarget]

lemma vertex_mem (i : Fin 5) : Data.quiver3.e k i ∈ normalSpan Data.quiver3 k (normal k) := by
  have H : Data.quiver3.e k i = normal k (normalIndex i i) := by
    fin_cases i <;> simp [normal,normalIndex,normalSource,normalPath,walk,word]
  rw [H]
  exact normal_mem (normal k) _
lemma vertex_span (i : Fin 5) (c : Fin 15) :
    Data.quiver3.e k i * normal k c ∈ normalSpan Data.quiver3 k (normal k) := by
  rw [normal,Data.quiver3.vertex_walk k i _ _ _ (normal_endpoints c)]
  split_ifs
  · exact normal_mem (normal k) c
  · exact Submodule.zero_mem _
end UniserialComputations.Uniform.Case3.Presentation
