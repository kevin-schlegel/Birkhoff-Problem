import Case3PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case3.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_10 (b : Fin Data.quiver3.arrows) : Data.quiver3.a k b * normal k 10 ∈ normalSpan Data.quiver3 k (normal k) := by
  fin_cases b
  · exact (Data.quiver3.arrow_incompatible k 0 3 2 _ (normal_endpoints 10) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · have H : Data.quiver3.a k 1 * normal k 10 = normal k 7 := by
      change Data.quiver3.a k 1 * Data.quiver3.walk k 3 [2] = Data.quiver3.walk k 3 [2,1]
      rw [← Data.quiver3.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 7
  · exact (Data.quiver3.arrow_incompatible k 2 3 2 _ (normal_endpoints 10) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · exact (Data.quiver3.arrow_incompatible k 3 3 2 _ (normal_endpoints 10) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
end UniserialComputations.Uniform.Case3.Presentation
