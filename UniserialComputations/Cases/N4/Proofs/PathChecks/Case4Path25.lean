import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_25 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 25 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · exact (Data.quiver4.arrow_incompatible k 0 5 3 _ (normal_endpoints 25) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 1 5 3 _ (normal_endpoints 25) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · have H : Data.quiver4.a k 2 * normal k 25 = normal k 20 := by
      change Data.quiver4.a k 2 * Data.quiver4.walk k 5 [4] = Data.quiver4.walk k 5 [4,2]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 20
  · exact (Data.quiver4.arrow_incompatible k 3 5 3 _ (normal_endpoints 25) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 4 5 3 _ (normal_endpoints 25) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 5 5 3 _ (normal_endpoints 25) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 6 5 3 _ (normal_endpoints 25) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 5 3 _ (normal_endpoints 25) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 5 3 _ (normal_endpoints 25) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
