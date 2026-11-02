import Case2PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case2.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_4 (b : Fin Data.quiver2.arrows) : Data.quiver2.a k b * normal k 4 ∈ normalSpan Data.quiver2 k (normal k) := by
  fin_cases b
  · have H : Data.quiver2.a k 0 * normal k 4 = normal k 2 := by
      change Data.quiver2.a k 0 * Data.quiver2.walk k 2 [1] = Data.quiver2.walk k 2 [1,0]
      rw [← Data.quiver2.walk_snoc]
      rfl
    exact H.symm ▸ normal_mem (normal k) 2
  · exact (Data.quiver2.arrow_incompatible k 1 2 1 _ (normal_endpoints 4) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver2 k (normal k)))
end UniserialComputations.Uniform.Case2.Presentation
