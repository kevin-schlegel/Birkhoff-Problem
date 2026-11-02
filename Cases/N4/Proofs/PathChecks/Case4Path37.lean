import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_37 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 37 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · exact (Data.quiver4.arrow_incompatible k 0 8 5 _ (normal_endpoints 37) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 1 8 5 _ (normal_endpoints 37) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 2 8 5 _ (normal_endpoints 37) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 3 8 5 _ (normal_endpoints 37) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · have H : Data.quiver4.a k 4 * normal k 37 = normal k 28 := by
      change Data.quiver4.a k 4 * Data.quiver4.walk k 8 [8,7,6] = Data.quiver4.walk k 8 [8,7,6,4]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 28
  · have H : Data.quiver4.a k 5 * normal k 37 = normal k 33 := by
      change Data.quiver4.a k 5 * Data.quiver4.walk k 8 [8,7,6] = Data.quiver4.walk k 8 [8,7,6,5]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 33
  · exact (Data.quiver4.arrow_incompatible k 6 8 5 _ (normal_endpoints 37) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 8 5 _ (normal_endpoints 37) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 8 5 _ (normal_endpoints 37) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
