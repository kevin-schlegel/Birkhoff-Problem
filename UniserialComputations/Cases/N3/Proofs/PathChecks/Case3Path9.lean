import Case3PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case3.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_9 (b : Fin Data.quiver3.arrows) : Data.quiver3.a k b * normal k 9 ∈ normalSpan Data.quiver3 k (normal k) := by
  fin_cases b
  · exact (Data.quiver3.arrow_incompatible k 0 2 2 _ (normal_endpoints 9) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · have H : Data.quiver3.a k 1 * normal k 9 = normal k 6 := by
      change Data.quiver3.a k 1 * Data.quiver3.walk k 2 [] = Data.quiver3.walk k 2 [1]
      rw [← Data.quiver3.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 6
  · exact (Data.quiver3.arrow_incompatible k 2 2 2 _ (normal_endpoints 9) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · exact (Data.quiver3.arrow_incompatible k 3 2 2 _ (normal_endpoints 9) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
end UniserialComputations.Uniform.Case3.Presentation
