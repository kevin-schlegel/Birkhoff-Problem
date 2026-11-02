import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_31 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 31 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · exact (Data.quiver4.arrow_incompatible k 0 6 4 _ (normal_endpoints 31) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 1 6 4 _ (normal_endpoints 31) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 2 6 4 _ (normal_endpoints 31) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · have H : Data.quiver4.a k 3 * normal k 31 = normal k 21 := by
      change Data.quiver4.a k 3 * Data.quiver4.walk k 6 [6,5] = Data.quiver4.walk k 6 [6,4,2]
      rw [← Data.quiver4.walk_snoc]
      change Data.quiver4.word (Data.quiver4.a k) ([6]++[5,3]++[]) * Data.quiver4.e k 6 = Data.quiver4.word (Data.quiver4.a k) ([6]++[4,2]++[]) * Data.quiver4.e k 6
      rw [diamond_context]
    exact H.symm ▸ normal_mem (normal k) 21
  · exact (Data.quiver4.arrow_incompatible k 4 6 4 _ (normal_endpoints 31) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 5 6 4 _ (normal_endpoints 31) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 6 6 4 _ (normal_endpoints 31) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 6 4 _ (normal_endpoints 31) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 6 4 _ (normal_endpoints 31) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
