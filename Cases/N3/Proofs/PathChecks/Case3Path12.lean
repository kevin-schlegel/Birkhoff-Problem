import Case3PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case3.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_12 (b : Fin Data.quiver3.arrows) : Data.quiver3.a k b * normal k 12 ∈ normalSpan Data.quiver3 k (normal k) := by
  fin_cases b
  · exact (Data.quiver3.arrow_incompatible k 0 3 3 _ (normal_endpoints 12) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · exact (Data.quiver3.arrow_incompatible k 1 3 3 _ (normal_endpoints 12) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · have H : Data.quiver3.a k 2 * normal k 12 = normal k 10 := by
      change Data.quiver3.a k 2 * Data.quiver3.walk k 3 [] = Data.quiver3.walk k 3 [2]
      rw [← Data.quiver3.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 10
  · exact (Data.quiver3.arrow_incompatible k 3 3 3 _ (normal_endpoints 12) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
end UniserialComputations.Uniform.Case3.Presentation
