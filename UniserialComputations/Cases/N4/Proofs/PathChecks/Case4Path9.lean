import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_9 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 9 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · have H : Data.quiver4.a k 0 * normal k 9 = normal k 1 := by
      change Data.quiver4.a k 0 * Data.quiver4.walk k 1 [] = Data.quiver4.walk k 1 [0]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 1
  · exact (Data.quiver4.arrow_incompatible k 1 1 1 _ (normal_endpoints 9) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 2 1 1 _ (normal_endpoints 9) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 3 1 1 _ (normal_endpoints 9) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 4 1 1 _ (normal_endpoints 9) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 5 1 1 _ (normal_endpoints 9) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 6 1 1 _ (normal_endpoints 9) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 1 1 _ (normal_endpoints 9) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 1 1 _ (normal_endpoints 9) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
