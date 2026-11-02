import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_13 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 13 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · have H : Data.quiver4.a k 0 * normal k 13 = normal k 5 := by
      change Data.quiver4.a k 0 * Data.quiver4.walk k 5 [4,2,1] = Data.quiver4.walk k 5 [4,2,1,0]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 5
  · exact (Data.quiver4.arrow_incompatible k 1 5 1 _ (normal_endpoints 13) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 2 5 1 _ (normal_endpoints 13) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 3 5 1 _ (normal_endpoints 13) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 4 5 1 _ (normal_endpoints 13) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 5 5 1 _ (normal_endpoints 13) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 6 5 1 _ (normal_endpoints 13) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 5 1 _ (normal_endpoints 13) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 5 1 _ (normal_endpoints 13) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
