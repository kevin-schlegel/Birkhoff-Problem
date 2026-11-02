import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_35 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 35 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · exact (Data.quiver4.arrow_incompatible k 0 6 5 _ (normal_endpoints 35) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 1 6 5 _ (normal_endpoints 35) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 2 6 5 _ (normal_endpoints 35) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 3 6 5 _ (normal_endpoints 35) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · have H : Data.quiver4.a k 4 * normal k 35 = normal k 26 := by
      change Data.quiver4.a k 4 * Data.quiver4.walk k 6 [6] = Data.quiver4.walk k 6 [6,4]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 26
  · have H : Data.quiver4.a k 5 * normal k 35 = normal k 31 := by
      change Data.quiver4.a k 5 * Data.quiver4.walk k 6 [6] = Data.quiver4.walk k 6 [6,5]
      rw [← Data.quiver4.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 31
  · exact (Data.quiver4.arrow_incompatible k 6 6 5 _ (normal_endpoints 35) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 6 5 _ (normal_endpoints 35) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 6 5 _ (normal_endpoints 35) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
