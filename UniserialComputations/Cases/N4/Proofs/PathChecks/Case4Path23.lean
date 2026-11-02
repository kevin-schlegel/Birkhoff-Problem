import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_23 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 23 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · exact (Data.quiver4.arrow_incompatible k 0 8 2 _ (normal_endpoints 23) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · have H : Data.quiver4.a k 1 * normal k 23 = normal k 16 := by
      change Data.quiver4.a k 1 * Data.quiver4.walk k 8 [8,7,6,4,2] = Data.quiver4.walk k 8 [8,7,6,4,2,1]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 16
  · exact (Data.quiver4.arrow_incompatible k 2 8 2 _ (normal_endpoints 23) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 3 8 2 _ (normal_endpoints 23) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 4 8 2 _ (normal_endpoints 23) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 5 8 2 _ (normal_endpoints 23) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 6 8 2 _ (normal_endpoints 23) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 8 2 _ (normal_endpoints 23) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 8 2 _ (normal_endpoints 23) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
