import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_16 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 16 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · have H : Data.quiver4.a k 0 * normal k 16 = normal k 8 := by
      change Data.quiver4.a k 0 * Data.quiver4.walk k 8 [8,7,6,4,2,1] = Data.quiver4.walk k 8 [8,7,6,4,2,1,0]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 8
  · exact (Data.quiver4.arrow_incompatible k 1 8 1 _ (normal_endpoints 16) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 2 8 1 _ (normal_endpoints 16) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 3 8 1 _ (normal_endpoints 16) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 4 8 1 _ (normal_endpoints 16) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 5 8 1 _ (normal_endpoints 16) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 6 8 1 _ (normal_endpoints 16) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 8 1 _ (normal_endpoints 16) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 8 1 _ (normal_endpoints 16) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
