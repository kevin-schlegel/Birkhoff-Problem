import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_24 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 24 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · exact (Data.quiver4.arrow_incompatible k 0 3 3 _ (normal_endpoints 24) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 1 3 3 _ (normal_endpoints 24) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · have H : Data.quiver4.a k 2 * normal k 24 = normal k 18 := by
      change Data.quiver4.a k 2 * Data.quiver4.walk k 3 [] = Data.quiver4.walk k 3 [2]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 18
  · exact (Data.quiver4.arrow_incompatible k 3 3 3 _ (normal_endpoints 24) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 4 3 3 _ (normal_endpoints 24) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 5 3 3 _ (normal_endpoints 24) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 6 3 3 _ (normal_endpoints 24) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 3 3 _ (normal_endpoints 24) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 3 3 _ (normal_endpoints 24) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
