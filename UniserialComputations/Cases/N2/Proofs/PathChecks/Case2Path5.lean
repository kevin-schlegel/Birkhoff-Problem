import Case2PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case2.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_5 (b : Fin Data.quiver2.arrows) : Data.quiver2.a k b * normal k 5 ∈ normalSpan Data.quiver2 k (normal k) := by
  fin_cases b
  · exact (Data.quiver2.arrow_incompatible k 0 2 2 _ (normal_endpoints 5) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver2 k (normal k)))
  · have H : Data.quiver2.a k 1 * normal k 5 = normal k 4 := by
      change Data.quiver2.a k 1 * Data.quiver2.walk k 2 [] = Data.quiver2.walk k 2 [1]
      rw [← Data.quiver2.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 4
end UniserialComputations.Uniform.Case2.Presentation
