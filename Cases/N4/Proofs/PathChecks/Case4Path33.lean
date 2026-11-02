import Case4PresentationBase
noncomputable section
namespace UniserialComputations.Uniform.Case4.Presentation
open QuiverData
variable (k : Type*) [Field k]
lemma arrow_span_33 (b : Fin Data.quiver4.arrows) : Data.quiver4.a k b * normal k 33 ∈ normalSpan Data.quiver4 k (normal k) := by
  fin_cases b
  · exact (Data.quiver4.arrow_incompatible k 0 8 4 _ (normal_endpoints 33) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 1 8 4 _ (normal_endpoints 33) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 2 8 4 _ (normal_endpoints 33) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · have H : Data.quiver4.a k 3 * normal k 33 = normal k 23 := by
      change Data.quiver4.a k 3 * Data.quiver4.walk k 8 [8,7,6,5] = Data.quiver4.walk k 8 [8,7,6,4,2]
      rw [← Data.quiver4.walk_snoc]
      change Data.quiver4.word (Data.quiver4.a k) ([8,7,6]++[5,3]++[]) * Data.quiver4.e k 8 = Data.quiver4.word (Data.quiver4.a k) ([8,7,6]++[4,2]++[]) * Data.quiver4.e k 8
      rw [diamond_context]
    exact H.symm ▸ normal_mem (normal k) 23
  · exact (Data.quiver4.arrow_incompatible k 4 8 4 _ (normal_endpoints 33) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 5 8 4 _ (normal_endpoints 33) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 6 8 4 _ (normal_endpoints 33) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 7 8 4 _ (normal_endpoints 33) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
  · exact (Data.quiver4.arrow_incompatible k 8 8 4 _ (normal_endpoints 33) (by decide)).symm ▸ (Submodule.zero_mem (normalSpan Data.quiver4 k (normal k)))
end UniserialComputations.Uniform.Case4.Presentation
