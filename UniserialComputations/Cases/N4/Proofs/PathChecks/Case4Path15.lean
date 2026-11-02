import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_15 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 15 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · have H : Data.quiver4.a k 0 * normal k 15 = normal k 7 := by
      change Data.quiver4.a k 0 * Data.quiver4.walk k 7 [7,6,4,2,1] = Data.quiver4.walk k 7 [7,6,4,2,1,0]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 7
  · exact (Data.quiver4.arrow_incompatible k 1 7 1 _ (normal_endpoints 15) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 2 7 1 _ (normal_endpoints 15) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 3 7 1 _ (normal_endpoints 15) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 4 7 1 _ (normal_endpoints 15) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 5 7 1 _ (normal_endpoints 15) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 6 7 1 _ (normal_endpoints 15) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 7 1 _ (normal_endpoints 15) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 7 1 _ (normal_endpoints 15) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
