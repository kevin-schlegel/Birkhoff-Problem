import Case3PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case3.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_4 (b : Fin Data.quiver3.arrows) : Data.quiver3.a k b * normal k 4 ∈ normalSpan Data.quiver3 k (normal k) := by
  fin_cases b
  · exact (Data.quiver3.arrow_incompatible k 0 4 0 _ (normal_endpoints 4) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · exact (Data.quiver3.arrow_incompatible k 1 4 0 _ (normal_endpoints 4) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · exact (Data.quiver3.arrow_incompatible k 2 4 0 _ (normal_endpoints 4) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · exact (Data.quiver3.arrow_incompatible k 3 4 0 _ (normal_endpoints 4) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
end UniserialComputations.Uniform.Case3.Presentation
