import Case3PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case3.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_1 (b : Fin Data.quiver3.arrows) : Data.quiver3.a k b * normal k 1 ∈ normalSpan Data.quiver3 k (normal k) := by
  fin_cases b
  · exact (Data.quiver3.arrow_incompatible k 0 1 0 _ (normal_endpoints 1) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · exact (Data.quiver3.arrow_incompatible k 1 1 0 _ (normal_endpoints 1) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · exact (Data.quiver3.arrow_incompatible k 2 1 0 _ (normal_endpoints 1) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
  · exact (Data.quiver3.arrow_incompatible k 3 1 0 _ (normal_endpoints 1) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver3 k (normal k)))
end UniserialComputations.Uniform.Case3.Presentation
