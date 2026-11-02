import Case2Path0
import Case2Path1
import Case2Path2
import Case2Path3
import Case2Path4
import Case2Path5

noncomputable section
namespace UniserialComputations.Uniform.Case2.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma finite_and_bound : Module.Finite k (Data.quiver2.Presented k) ∧ Module.finrank k (Data.quiver2.Presented k) ≤ 6 := by
  apply finite_of_span_top (normal k)
  apply span_top (normal k)
  · rw [← Data.quiver2.sum_e k]
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
instance : Module.Finite k (Data.quiver2.Presented k) := (finite_and_bound k).1

lemma pathMap_surjective : Function.Surjective (pathMap k) := by
  intro T
  refine ⟨∑ i : Fin 3, ∑ j : Fin 3, if hij : Allowed i j then T.val i j • pathNormal k (normalIndex i j) else 0, ?_⟩
  apply Subtype.ext
  change (N2.endAlgebra k).val (pathMap k (∑ i : Fin 3, ∑ j : Fin 3, if hij : Allowed i j then T.val i j • pathNormal k (normalIndex i j) else 0)) = T.val
  simp only [map_sum]
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3, Matrix.single i j (T.val i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : Allowed i j
      · simp only [dif_pos hij,map_smul]
        change T.val i j • (pathMap k (pathNormal k (normalIndex i j))).val = _
        rw [path_image, (normalIndex_spec i j hij).1, (normalIndex_spec i j hij).2]
        simp
      · have hz : T.val i j = 0 := T.property i j (by omega)
        simp [hij,hz]
    _ = T.val := Matrix.sum_sum_single _

lemma evaluate_surjective : Function.Surjective (evaluate k) := by
  intro T
  obtain ⟨p,hp⟩ := pathMap_surjective k T
  exact ⟨Data.quiver2.q k p,hp⟩
theorem presented_dimension : Module.finrank k (Data.quiver2.Presented k) = 6 := by
  apply le_antisymm (finite_and_bound k).2
  have H := LinearMap.finrank_le_finrank_of_surjective (show Function.Surjective (evaluate k).toLinearMap from evaluate_surjective k)
  simpa only [N2.end_dimension k] using H
end UniserialComputations.Uniform.Case2.Presentation
