import Case4Path0
import Case4Path1
import Case4Path2
import Case4Path3
import Case4Path4
import Case4Path5
import Case4Path6
import Case4Path7
import Case4Path8
import Case4Path9
import Case4Path10
import Case4Path11
import Case4Path12
import Case4Path13
import Case4Path14
import Case4Path15
import Case4Path16
import Case4Path17
import Case4Path18
import Case4Path19
import Case4Path20
import Case4Path21
import Case4Path22
import Case4Path23
import Case4Path24
import Case4Path25
import Case4Path26
import Case4Path27
import Case4Path28
import Case4Path29
import Case4Path30
import Case4Path31
import Case4Path32
import Case4Path33
import Case4Path34
import Case4Path35
import Case4Path36
import Case4Path37
import Case4Path38
import Case4Path39
import Case4Path40
import Case4Path41
import Case4Path42
import Case4Path43

noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma finite_and_bound : Module.Finite k (Data.quiver4.Presented k) ∧ Module.finrank k (Data.quiver4.Presented k) ≤ 44 := by
  apply finite_of_span_top (normal k)
  apply span_top (normal k)
  · rw [← Data.quiver4.sum_e k]
    exact Submodule.sum_mem _ (fun i _ => vertex_mem k i)
  · exact vertex_span k
  · intro b c
    fin_cases c
    · exact arrow_span_0 k b
    · exact arrow_span_1 k b
    · exact arrow_span_2 k b
    · exact arrow_span_3 k b
    · exact arrow_span_4 k b
    · exact arrow_span_5 k b
    · exact arrow_span_6 k b
    · exact arrow_span_7 k b
    · exact arrow_span_8 k b
    · exact arrow_span_9 k b
    · exact arrow_span_10 k b
    · exact arrow_span_11 k b
    · exact arrow_span_12 k b
    · exact arrow_span_13 k b
    · exact arrow_span_14 k b
    · exact arrow_span_15 k b
    · exact arrow_span_16 k b
    · exact arrow_span_17 k b
    · exact arrow_span_18 k b
    · exact arrow_span_19 k b
    · exact arrow_span_20 k b
    · exact arrow_span_21 k b
    · exact arrow_span_22 k b
    · exact arrow_span_23 k b
    · exact arrow_span_24 k b
    · exact arrow_span_25 k b
    · exact arrow_span_26 k b
    · exact arrow_span_27 k b
    · exact arrow_span_28 k b
    · exact arrow_span_29 k b
    · exact arrow_span_30 k b
    · exact arrow_span_31 k b
    · exact arrow_span_32 k b
    · exact arrow_span_33 k b
    · exact arrow_span_34 k b
    · exact arrow_span_35 k b
    · exact arrow_span_36 k b
    · exact arrow_span_37 k b
    · exact arrow_span_38 k b
    · exact arrow_span_39 k b
    · exact arrow_span_40 k b
    · exact arrow_span_41 k b
    · exact arrow_span_42 k b
    · exact arrow_span_43 k b
instance : Module.Finite k (Data.quiver4.Presented k) := (finite_and_bound k).1

lemma pathMap_surjective : Function.Surjective (pathMap k) := by
  intro T
  refine ⟨∑ i : Fin 9, ∑ j : Fin 9, if hij : Allowed i j then T.val i j • pathNormal k (normalIndex i j) else 0, ?_⟩
  apply Subtype.ext
  change (N4.endAlgebra k).val (pathMap k (∑ i : Fin 9, ∑ j : Fin 9, if hij : Allowed i j then T.val i j • pathNormal k (normalIndex i j) else 0)) = T.val
  simp only [map_sum]
  calc
    _ = ∑ i : Fin 9, ∑ j : Fin 9, Matrix.single i j (T.val i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : Allowed i j
      · simp only [dif_pos hij,map_smul]
        change T.val i j • (pathMap k (pathNormal k (normalIndex i j))).val = _
        rw [path_image, (normalIndex_spec i j hij).1, (normalIndex_spec i j hij).2]
        simp
      · have hz : T.val i j = 0 := T.property i j hij
        simp [hij,hz]
    _ = T.val := Matrix.sum_sum_single _

lemma evaluate_surjective : Function.Surjective (evaluate k) := by
  intro T
  obtain ⟨p,hp⟩ := pathMap_surjective k T
  exact ⟨Data.quiver4.q k p,hp⟩
theorem presented_dimension : Module.finrank k (Data.quiver4.Presented k) = 44 := by
  apply le_antisymm (finite_and_bound k).2
  have H := LinearMap.finrank_le_finrank_of_surjective (show Function.Surjective (evaluate k).toLinearMap from evaluate_surjective k)
  simpa only [N4.end_dimension k] using H
end UniserialComputations.Uniform.Case4.Presentation
