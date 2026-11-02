import Case4Quiver
import UniformMatrixPaths
import Final

noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (k : Type*) [Field k]
abbrev Allowed (i j : Fin 9) : Prop := N4.Allowed i j
lemma single_mem (i j : Fin 9) (h : Allowed i j) : Matrix.single i j (1:k) ∈ N4.endAlgebra k := by
  intro a b hab
  simp only [Matrix.single_apply]
  split_ifs with hh
  · obtain ⟨rfl,rfl⟩ := hh
    exact (hab h).elim
  · rfl
def representation : Data.quiver4.Representation k (N4.End k) :=
  Data.quiver4.matrixRepresentation k (N4.endAlgebra k)
    (fun i => single_mem k i i (by exact ⟨le_rfl,by omega⟩))
    (fun b => single_mem k _ _ (by fin_cases b <;> decide))
abbrev pathMap := (representation k).pathMap

lemma relations_zero (z : Fin Data.quiver4.relations.length) :
    pathMap k (Data.quiver4.polynomial (Data.quiver4.arrow k) Data.quiver4.relations[z])=0 := by
  fin_cases z
  change pathMap k (Data.quiver4.polynomial (Data.quiver4.arrow k) [(1,[4,2]),(-1,[5,3])]) = 0
  simp only [QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,one_zsmul,neg_one_zsmul,mul_one,add_zero]
  simp only [map_add,map_neg,map_mul,Representation.pathMap_arrow]
  apply Subtype.ext
  norm_num [representation,matrixRepresentation,Data.quiver4,Subalgebra.coe_mul,Subalgebra.coe_add,Subalgebra.coe_neg]
def evaluate : Data.quiver4.Presented k →ₐ[k] N4.End k :=
  (representation k).evaluate (relations_zero k)
abbrev normalSource : Fin 44 → Fin 9 := ![0,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,2,3,4,5,6,7,8,3,5,6,7,8,4,5,6,7,8,5,6,7,8,6,7,8,7,8,8]
abbrev normalTarget : Fin 44 → Fin 9 := ![0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,3,3,3,3,3,4,4,4,4,4,5,5,5,5,6,6,6,7,7,8]
abbrev normalPath : Fin 44 → List (Fin Data.quiver4.arrows) := ![[],[0],[1,0],[2,1,0],[3,1,0],[4,2,1,0],[6,4,2,1,0],[7,6,4,2,1,0],[8,7,6,4,2,1,0],[],[1],[2,1],[3,1],[4,2,1],[6,4,2,1],[7,6,4,2,1],[8,7,6,4,2,1],[],[2],[3],[4,2],[6,4,2],[7,6,4,2],[8,7,6,4,2],[],[4],[6,4],[7,6,4],[8,7,6,4],[],[5],[6,5],[7,6,5],[8,7,6,5],[],[6],[7,6],[8,7,6],[],[7],[8,7],[],[8],[]]
abbrev normalIndex : Fin 9 → Fin 9 → Fin 44 := ![![0,1,2,3,4,5,6,7,8],![0,9,10,11,12,13,14,15,16],![0,0,17,18,19,20,21,22,23],![0,0,0,24,0,25,26,27,28],![0,0,0,0,29,30,31,32,33],![0,0,0,0,0,34,35,36,37],![0,0,0,0,0,0,38,39,40],![0,0,0,0,0,0,0,41,42],![0,0,0,0,0,0,0,0,43]]
theorem normalIndex_spec : ∀ i j, Allowed i j →
    normalTarget (normalIndex i j)=i ∧ normalSource (normalIndex i j)=j := by decide
theorem normal_endpoints : ∀ c, Data.quiver4.walkEnd (normalSource c) (normalPath c)=some (normalTarget c) := by decide
def normal (c : Fin 44) : Data.quiver4.Presented k := Data.quiver4.walk k (normalSource c) (normalPath c)
def pathNormal (c : Fin 44) : Data.quiver4.PathAlgebra k :=
  Data.quiver4.word (Data.quiver4.arrow k) (normalPath c) * Data.quiver4.vertex k (normalSource c)
lemma path_image (c : Fin 44) : (pathMap k (pathNormal k c)).val = Matrix.single (normalTarget c) (normalSource c) 1 := by
  rw [pathNormal,Representation.pathMap_walk]
  fin_cases c
  all_goals simp [word,representation,matrixRepresentation,Data.quiver4,normalPath,normalSource,normalTarget]

lemma vertex_mem (i : Fin 9) : Data.quiver4.e k i ∈ normalSpan Data.quiver4 k (normal k) := by
  have H : Data.quiver4.e k i = normal k (normalIndex i i) := by
    fin_cases i <;> simp [normal,normalIndex,normalSource,normalPath,walk,word]
  rw [H]
  exact normal_mem (normal k) _
lemma vertex_span (i : Fin 9) (c : Fin 44) :
    Data.quiver4.e k i * normal k c ∈ normalSpan Data.quiver4 k (normal k) := by
  rw [normal,Data.quiver4.vertex_walk k i _ _ _ (normal_endpoints c)]
  split_ifs
  · exact normal_mem (normal k) c
  · exact Submodule.zero_mem _
lemma diamond : Data.quiver4.word (Data.quiver4.a k) [5,3] = Data.quiver4.word (Data.quiver4.a k) [4,2] := by
  have H := Data.quiver4.relation_zero k 0
  change Data.quiver4.polynomial (Data.quiver4.a k) [(1,[4,2]),(-1,[5,3])] = 0 at H
  have H' : Data.quiver4.word (Data.quiver4.a k) [4,2] + -Data.quiver4.word (Data.quiver4.a k) [5,3] = 0 := by
    simpa only [QuiverData.polynomial,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      one_zsmul,neg_one_zsmul,add_zero,sub_eq_add_neg] using H
  exact (eq_of_add_neg_eq_zero H').symm
lemma diamond_context (p t : List (Fin 9)) :
    Data.quiver4.word (Data.quiver4.a k) (p++[5,3]++t) =
    Data.quiver4.word (Data.quiver4.a k) (p++[4,2]++t) := by
  simp only [Data.quiver4.word_append]
  rw [diamond k]
end UniserialComputations.Uniform.Case4.Presentation
