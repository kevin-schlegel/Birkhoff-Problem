import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_30 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 30 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · exact (Data.quiver4.arrow_incompatible k 0 5 4 _ (normal_endpoints 30) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 1 5 4 _ (normal_endpoints 30) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 2 5 4 _ (normal_endpoints 30) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · have H : Data.quiver4.a k 3 * normal k 30 = normal k 20 := by
      change Data.quiver4.a k 3 * Data.quiver4.walk k 5 [5] = Data.quiver4.walk k 5 [4,2]
      rw [← Data.quiver4.walk_snoc]
      change Data.quiver4.word (Data.quiver4.a k) ([]++[5,3]++[]) * Data.quiver4.e k 5 = Data.quiver4.word (Data.quiver4.a k) ([]++[4,2]++[]) * Data.quiver4.e k 5
      rw [diamond_context]
    exact H.symm ▸ normal_mem (normal k) 20
  · exact (Data.quiver4.arrow_incompatible k 4 5 4 _ (normal_endpoints 30) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 5 5 4 _ (normal_endpoints 30) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 6 5 4 _ (normal_endpoints 30) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 5 4 _ (normal_endpoints 30) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 5 4 _ (normal_endpoints 30) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
