import Case3PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case3.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_14 (b : Fin Data.quiver3.arrows) : Data.quiver3.a k b * normal k 14 ∈ normalSpan Data.quiver3 k (normal k) := by
  fin_cases b
  · exact (Data.quiver3.arrow_incompatible k 0 4 4 _ (normal_endpoints 14) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · exact (Data.quiver3.arrow_incompatible k 1 4 4 _ (normal_endpoints 14) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · exact (Data.quiver3.arrow_incompatible k 2 4 4 _ (normal_endpoints 14) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · have H : Data.quiver3.a k 3 * normal k 14 = normal k 13 := by
      change Data.quiver3.a k 3 * Data.quiver3.walk k 4 [] = Data.quiver3.walk k 4 [3]
      rw [← Data.quiver3.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 13
end UniserialComputations.Uniform.Case3.Presentation
