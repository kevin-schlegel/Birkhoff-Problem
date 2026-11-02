import Case6PathEquiv
noncomputable section
namespace UniserialComputations.Uniform.Case6.Presentation
open QuiverData
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
theorem terms_eq : ∀ z : Fin 47, Data.quiver6.relations[z] = N6.relationTerms z := by decide
lemma relations_forward (x y : Data.quiver6.PathAlgebra k) (H : Data.quiver6.Relations k x y) :
    N6.Presentation.q k (pathEquiv k x) = N6.Presentation.q k (pathEquiv k y) := by
  cases H with
  | relation z =>
    have hm : N6.Presentation.q k (pathEquiv k (Data.quiver6.polynomial (Data.quiver6.arrow k) Data.quiver6.relations[z])) =
        Data.quiver6.polynomial (N6.Presentation.a k) Data.quiver6.relations[z] := by
      simp only [QuiverData.polynomial,QuiverData.word,map_list_sum,map_zsmul,map_list_prod,List.map_map,Function.comp_def,pathEquiv_arrow]
      rfl
    rw [hm,map_zero,map_zero]
    change Data.quiver6.polynomial (N6.Presentation.a k) Data.quiver6.relations[z] = 0
    rw [terms_eq z]
    exact N6.Presentation.relation_zero k z
lemma relations_backward (x y : N6.Presentation.PathAlgebra k) (H : N6.Presentation.Relations k x y) :
    Data.quiver6.q k ((pathEquiv k).symm x) = Data.quiver6.q k ((pathEquiv k).symm y) := by
  cases H with
  | relation z =>
    have hm : Data.quiver6.q k ((pathEquiv k).symm (N6.Presentation.polynomial (N6.Presentation.pathArrow k) (N6.relationTerms z))) =
        Data.quiver6.polynomial (Data.quiver6.a k) (N6.relationTerms z) := by
      simp only [N6.Presentation.polynomial,N6.Presentation.word,QuiverData.polynomial,QuiverData.word,map_list_sum,map_zsmul,map_list_prod,List.map_map,Function.comp_def,pathEquiv_symm_arrow]
      rfl
    rw [hm,map_zero,map_zero]
    change Data.quiver6.polynomial (Data.quiver6.a k) (N6.relationTerms z) = 0
    rw [← terms_eq z]
    exact Data.quiver6.relation_zero k z

end UniserialComputations.Uniform.Case6.Presentation
