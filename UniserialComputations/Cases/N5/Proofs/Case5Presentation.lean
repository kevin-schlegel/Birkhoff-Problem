import Case5Quiver
import UniformPresentationEquiv
import UniformMatrixPaths
import N5Presentation

noncomputable section
namespace UniserialComputations.Uniform.Case5.Presentation
open QuiverData
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]

def pathEquiv : Data.quiver5.PathAlgebra k ≃ₐ[k] N5.PathAlgebra k :=
  presentationEquiv k ((AlgEquiv.refl : Data.quiver5.Free k ≃ₐ[k] Data.quiver5.Free k)) (Data.quiver5.PathRelations k) (N5.PathRelations k)
    (by
      intro x y H
      cases H with
      | vv i j => exact RingQuot.mkAlgHom_rel k (N5.PathRelations.vv i j)
      | va i b => exact RingQuot.mkAlgHom_rel k (N5.PathRelations.va i b)
      | av b i => exact RingQuot.mkAlgHom_rel k (N5.PathRelations.av b i)
      | unit => exact RingQuot.mkAlgHom_rel k (N5.PathRelations.unit))
    (by
      intro x y H
      cases H with
      | vv i j => exact RingQuot.mkAlgHom_rel k (QuiverData.PathRelations.vv (Q:=Data.quiver5) i j)
      | va i b => exact RingQuot.mkAlgHom_rel k (QuiverData.PathRelations.va (Q:=Data.quiver5) i b)
      | av b i => exact RingQuot.mkAlgHom_rel k (QuiverData.PathRelations.av (Q:=Data.quiver5) b i)
      | unit => exact RingQuot.mkAlgHom_rel k (QuiverData.PathRelations.unit (Q:=Data.quiver5)))

@[simp] lemma pathEquiv_vertex (i : Fin 18) : pathEquiv k (Data.quiver5.vertex k i) = N5.pathVertex k i := rfl
@[simp] lemma pathEquiv_arrow (b : Fin 23) : pathEquiv k (Data.quiver5.arrow k b) = N5.pathArrow k b := rfl
@[simp] lemma pathEquiv_symm_vertex (i : Fin 18) : (pathEquiv k).symm (N5.pathVertex k i) = Data.quiver5.vertex k i := rfl
@[simp] lemma pathEquiv_symm_arrow (b : Fin 23) : (pathEquiv k).symm (N5.pathArrow k b) = Data.quiver5.arrow k b := rfl
lemma new_zero_0 : Data.quiver5.a k (N5.Presentation.zeroPairs 0).2 * Data.quiver5.a k (N5.Presentation.zeroPairs 0).1 = 0 := by
  have H := Data.quiver5.relation_zero k 0
  simpa [Data.quiver5,N5.Presentation.zeroPairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using H
lemma new_commute_0 :
    Data.quiver5.a k (N5.Presentation.commutePairs 0).1.2 * Data.quiver5.a k (N5.Presentation.commutePairs 0).1.1 =
    Data.quiver5.a k (N5.Presentation.commutePairs 0).2.2 * Data.quiver5.a k (N5.Presentation.commutePairs 0).2.1 := by
  have H := Data.quiver5.relation_zero k 5
  apply sub_eq_zero.mp
  simpa [Data.quiver5,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using H
lemma new_zero_1 : Data.quiver5.a k (N5.Presentation.zeroPairs 1).2 * Data.quiver5.a k (N5.Presentation.zeroPairs 1).1 = 0 := by
  have H := Data.quiver5.relation_zero k 1
  simpa [Data.quiver5,N5.Presentation.zeroPairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using H
lemma new_commute_1 :
    Data.quiver5.a k (N5.Presentation.commutePairs 1).1.2 * Data.quiver5.a k (N5.Presentation.commutePairs 1).1.1 =
    Data.quiver5.a k (N5.Presentation.commutePairs 1).2.2 * Data.quiver5.a k (N5.Presentation.commutePairs 1).2.1 := by
  have H := Data.quiver5.relation_zero k 6
  apply sub_eq_zero.mp
  simpa [Data.quiver5,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using H
lemma new_zero_2 : Data.quiver5.a k (N5.Presentation.zeroPairs 2).2 * Data.quiver5.a k (N5.Presentation.zeroPairs 2).1 = 0 := by
  have H := Data.quiver5.relation_zero k 2
  simpa [Data.quiver5,N5.Presentation.zeroPairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using H
lemma new_commute_2 :
    Data.quiver5.a k (N5.Presentation.commutePairs 2).1.2 * Data.quiver5.a k (N5.Presentation.commutePairs 2).1.1 =
    Data.quiver5.a k (N5.Presentation.commutePairs 2).2.2 * Data.quiver5.a k (N5.Presentation.commutePairs 2).2.1 := by
  have H := Data.quiver5.relation_zero k 7
  apply sub_eq_zero.mp
  simpa [Data.quiver5,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using H
lemma new_zero_3 : Data.quiver5.a k (N5.Presentation.zeroPairs 3).2 * Data.quiver5.a k (N5.Presentation.zeroPairs 3).1 = 0 := by
  have H := Data.quiver5.relation_zero k 3
  simpa [Data.quiver5,N5.Presentation.zeroPairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using H
lemma new_commute_3 :
    Data.quiver5.a k (N5.Presentation.commutePairs 3).1.2 * Data.quiver5.a k (N5.Presentation.commutePairs 3).1.1 =
    Data.quiver5.a k (N5.Presentation.commutePairs 3).2.2 * Data.quiver5.a k (N5.Presentation.commutePairs 3).2.1 := by
  have H := Data.quiver5.relation_zero k 8
  apply sub_eq_zero.mp
  simpa [Data.quiver5,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using H
lemma new_zero_4 : Data.quiver5.a k (N5.Presentation.zeroPairs 4).2 * Data.quiver5.a k (N5.Presentation.zeroPairs 4).1 = 0 := by
  have H := Data.quiver5.relation_zero k 4
  simpa [Data.quiver5,N5.Presentation.zeroPairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using H
lemma new_commute_4 :
    Data.quiver5.a k (N5.Presentation.commutePairs 4).1.2 * Data.quiver5.a k (N5.Presentation.commutePairs 4).1.1 =
    Data.quiver5.a k (N5.Presentation.commutePairs 4).2.2 * Data.quiver5.a k (N5.Presentation.commutePairs 4).2.1 := by
  have H := Data.quiver5.relation_zero k 9
  apply sub_eq_zero.mp
  simpa [Data.quiver5,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using H
lemma relations_forward (x y : Data.quiver5.PathAlgebra k) (H : Data.quiver5.Relations k x y) :
    N5.Presentation.q k (pathEquiv k x) = N5.Presentation.q k (pathEquiv k y) := by
  cases H with
  | relation z =>
    have hm : N5.Presentation.q k (pathEquiv k (Data.quiver5.polynomial (Data.quiver5.arrow k) Data.quiver5.relations[z])) =
        Data.quiver5.polynomial (N5.Presentation.a k) Data.quiver5.relations[z] := by
      simp only [QuiverData.polynomial,QuiverData.word,map_list_sum,map_zsmul,map_list_prod,List.map_map,Function.comp_def,pathEquiv_arrow]
      rfl
    rw [hm,map_zero,map_zero]
    change Data.quiver5.polynomial (N5.Presentation.a k) Data.quiver5.relations[z] = 0
    fin_cases z
    · simpa [Data.quiver5,N5.Presentation.zeroPairs,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using (N5.Presentation.zero_rel k 0)
    · simpa [Data.quiver5,N5.Presentation.zeroPairs,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using (N5.Presentation.zero_rel k 1)
    · simpa [Data.quiver5,N5.Presentation.zeroPairs,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using (N5.Presentation.zero_rel k 2)
    · simpa [Data.quiver5,N5.Presentation.zeroPairs,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using (N5.Presentation.zero_rel k 3)
    · simpa [Data.quiver5,N5.Presentation.zeroPairs,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using (N5.Presentation.zero_rel k 4)
    · simpa [Data.quiver5,N5.Presentation.zeroPairs,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using (sub_eq_zero.mpr (N5.Presentation.commute_rel k 0))
    · simpa [Data.quiver5,N5.Presentation.zeroPairs,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using (sub_eq_zero.mpr (N5.Presentation.commute_rel k 1))
    · simpa [Data.quiver5,N5.Presentation.zeroPairs,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using (sub_eq_zero.mpr (N5.Presentation.commute_rel k 2))
    · simpa [Data.quiver5,N5.Presentation.zeroPairs,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using (sub_eq_zero.mpr (N5.Presentation.commute_rel k 3))
    · simpa [Data.quiver5,N5.Presentation.zeroPairs,N5.Presentation.commutePairs,QuiverData.polynomial,QuiverData.word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.prod_cons,List.prod_nil,mul_one,add_zero,one_zsmul,neg_one_zsmul,sub_eq_add_neg] using (sub_eq_zero.mpr (N5.Presentation.commute_rel k 4))
lemma relations_backward (x y : N5.PathAlgebra k) (H : N5.Presentation.Relations k x y) :
    Data.quiver5.q k ((pathEquiv k).symm x) = Data.quiver5.q k ((pathEquiv k).symm y) := by
  cases H with
  | zero z =>
    simp only [map_mul,map_zero,pathEquiv_symm_arrow]
    fin_cases z
    · exact new_zero_0 k
    · exact new_zero_1 k
    · exact new_zero_2 k
    · exact new_zero_3 k
    · exact new_zero_4 k
  | commute z =>
    simp only [map_mul,pathEquiv_symm_arrow]
    fin_cases z
    · exact new_commute_0 k
    · exact new_commute_1 k
    · exact new_commute_2 k
    · exact new_commute_3 k
    · exact new_commute_4 k
def presentedEquiv : Data.quiver5.Presented k ≃ₐ[k] N5.Presentation.Presented k :=
  presentationEquiv k (pathEquiv k) (Data.quiver5.Relations k) (N5.Presentation.Relations k)
    (relations_forward k) (relations_backward k)

instance : Module.Finite k (Data.quiver5.Presented k) := Module.Finite.of_surjective (presentedEquiv k).symm.toLinearMap (presentedEquiv k).symm.surjective
theorem presented_dimension : Module.finrank k (Data.quiver5.Presented k) = 179 :=
  (presentedEquiv k).toLinearEquiv.finrank_eq.trans (N5.Presentation.presented_dimension k)

def pathMap : Data.quiver5.PathAlgebra k →ₐ[k] N5.End k := (N5.pathMap k).comp (pathEquiv k).toAlgHom
theorem pathMap_surjective : Function.Surjective (pathMap k) :=
  (N5.pathMap_surjective k).comp (pathEquiv k).surjective
@[simp] theorem pathMap_vertex (i : Fin 18) : pathMap k (Data.quiver5.vertex k i) = N5.vertex k i := by
  change N5.pathMap k (pathEquiv k (Data.quiver5.vertex k i)) = _
  rw [pathEquiv_vertex]
  rfl
@[simp] theorem pathMap_arrow (b : Fin 23) : pathMap k (Data.quiver5.arrow k b) = N5.arrow k b := by
  change N5.pathMap k (pathEquiv k (Data.quiver5.arrow k b)) = _
  rw [pathEquiv_arrow]
  rfl

theorem relations_zero (z : Fin Data.quiver5.relations.length) :
    pathMap k (Data.quiver5.polynomial (Data.quiver5.arrow k) Data.quiver5.relations[z])=0 := by
  have H := congrArg (N5.Presentation.evaluate k) (relations_forward k _ _ (QuiverData.Relations.relation (Q:=Data.quiver5) z))
  change N5.pathMap k (pathEquiv k (Data.quiver5.polynomial (Data.quiver5.arrow k) Data.quiver5.relations[z])) =
    N5.pathMap k (pathEquiv k 0) at H
  rw [map_zero,map_zero] at H
  exact H

end UniserialComputations.Uniform.Case5.Presentation
