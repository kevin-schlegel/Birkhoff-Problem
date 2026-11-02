import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_34 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 34 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · exact (Data.quiver4.arrow_incompatible k 0 5 5 _ (normal_endpoints 34) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 1 5 5 _ (normal_endpoints 34) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 2 5 5 _ (normal_endpoints 34) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 3 5 5 _ (normal_endpoints 34) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · have H : Data.quiver4.a k 4 * normal k 34 = normal k 25 := by
      change Data.quiver4.a k 4 * Data.quiver4.walk k 5 [] = Data.quiver4.walk k 5 [4]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 25
  · have H : Data.quiver4.a k 5 * normal k 34 = normal k 30 := by
      change Data.quiver4.a k 5 * Data.quiver4.walk k 5 [] = Data.quiver4.walk k 5 [5]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 30
  · exact (Data.quiver4.arrow_incompatible k 6 5 5 _ (normal_endpoints 34) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 5 5 _ (normal_endpoints 34) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 5 5 _ (normal_endpoints 34) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
