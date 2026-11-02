import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_29 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 29 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · exact (Data.quiver4.arrow_incompatible k 0 4 4 _ (normal_endpoints 29) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 1 4 4 _ (normal_endpoints 29) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 2 4 4 _ (normal_endpoints 29) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · have H : Data.quiver4.a k 3 * normal k 29 = normal k 19 := by
      change Data.quiver4.a k 3 * Data.quiver4.walk k 4 [] = Data.quiver4.walk k 4 [3]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 19
  · exact (Data.quiver4.arrow_incompatible k 4 4 4 _ (normal_endpoints 29) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 5 4 4 _ (normal_endpoints 29) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 6 4 4 _ (normal_endpoints 29) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 4 4 _ (normal_endpoints 29) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 4 4 _ (normal_endpoints 29) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
