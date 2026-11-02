import Case2PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case2.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_1 (b : Fin Data.quiver2.arrows) : Data.quiver2.a k b * normal k 1 ∈ normalSpan Data.quiver2 k (normal k) := by
  fin_cases b
  · exact (Data.quiver2.arrow_incompatible k 0 1 0 _ (normal_endpoints 1) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver2 k (normal k)))
  · exact (Data.quiver2.arrow_incompatible k 1 1 0 _ (normal_endpoints 1) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver2 k (normal k)))
end UniserialComputations.Uniform.Case2.Presentation
