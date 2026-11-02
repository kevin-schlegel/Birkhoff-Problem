import Case3PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case3.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_7 (b : Fin Data.quiver3.arrows) : Data.quiver3.a k b * normal k 7 ∈ normalSpan Data.quiver3 k (normal k) := by
  fin_cases b
  · have H : Data.quiver3.a k 0 * normal k 7 = normal k 3 := by
      change Data.quiver3.a k 0 * Data.quiver3.walk k 3 [2,1] = Data.quiver3.walk k 3 [2,1,0]
      rw [← Data.quiver3.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 3
  · exact (Data.quiver3.arrow_incompatible k 1 3 1 _ (normal_endpoints 7) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · exact (Data.quiver3.arrow_incompatible k 2 3 1 _ (normal_endpoints 7) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · exact (Data.quiver3.arrow_incompatible k 3 3 1 _ (normal_endpoints 7) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
end UniserialComputations.Uniform.Case3.Presentation
