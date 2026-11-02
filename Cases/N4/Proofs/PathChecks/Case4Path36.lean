import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_36 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 36 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · exact (Data.quiver4.arrow_incompatible k 0 7 5 _ (normal_endpoints 36) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 1 7 5 _ (normal_endpoints 36) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 2 7 5 _ (normal_endpoints 36) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 3 7 5 _ (normal_endpoints 36) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · have H : Data.quiver4.a k 4 * normal k 36 = normal k 27 := by
      change Data.quiver4.a k 4 * Data.quiver4.walk k 7 [7,6] = Data.quiver4.walk k 7 [7,6,4]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 27
  · have H : Data.quiver4.a k 5 * normal k 36 = normal k 32 := by
      change Data.quiver4.a k 5 * Data.quiver4.walk k 7 [7,6] = Data.quiver4.walk k 7 [7,6,5]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 32
  · exact (Data.quiver4.arrow_incompatible k 6 7 5 _ (normal_endpoints 36) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 7 5 _ (normal_endpoints 36) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 7 5 _ (normal_endpoints 36) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
