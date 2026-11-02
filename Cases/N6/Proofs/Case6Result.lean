import Case6Dataset
import Case6Bridge
import Case6Presentation
import UniformResult

noncomputable section
namespace UniserialComputations.Uniform.Case6
variable (k : Type*) [Field k]
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

lemma vertex_image (i : Fin 47) :
    (Presentation.pathMap k (Data.quiver6.vertex k i)).val = Data.case6.vertexMatrix k i := by
  rw [Presentation.pathMap_vertex]
  ext r c
  change (N6.insert k i i (N6.unitBlock k i)) r c = (if r=c then if r.1=i then 1 else 0 else 0)
  by_cases hri : r.1=i
  · by_cases hci : c.1=i
    · subst i
      have hc : c.1=r.1 := hci
      rcases r with ⟨v,a⟩
      rcases c with ⟨w,b⟩
      dsimp at hc
      cases hc
      by_cases hab : a=b
      · cases hab
        simp [N6.insert,N6.assemble,N6.unitBlock,N6.part,Dataset.vertexMatrix,Data.case6,coordinates,Matrix.diagonal,a.isLt]
      · have hvab : a.val ≠ b.val := fun hh => hab (Fin.ext hh)
        simp [N6.insert,N6.assemble,N6.unitBlock,N6.part,Dataset.vertexMatrix,Data.case6,coordinates,Matrix.diagonal,hab,hvab]
    · have hrc : r ≠ c := by intro hrc; cases hrc; exact hci hri
      simp [N6.insert,N6.assemble,Dataset.vertexMatrix,Data.case6,coordinates,Matrix.diagonal,hci,hrc]
  · by_cases hrc : r=c
    · subst c
      simp [N6.insert,N6.assemble,Dataset.vertexMatrix,Data.case6,coordinates,Matrix.diagonal,hri]
    · simp [N6.insert,N6.assemble,Dataset.vertexMatrix,Data.case6,coordinates,Matrix.diagonal,hri,hrc]
lemma arrow_image (a : Fin Data.quiver6.arrows) :
    (Presentation.pathMap k (Data.quiver6.arrow k a)).val = Data.case6.arrowValue k a := by
  rw [Presentation.pathMap_arrow]
  have hb := N6.Presentation.castBlock_arrow k a
  ext r c
  change (N6.insert k (N6.arrowTarget a) (N6.arrowSource a) (N6.arrowMatrix k a)) r c =
    ((Data.arrows6 a r c : ℤ) : k)
  have hg : Data.arrows6 a r c =
      (if r.1=N6.arrowTarget a ∧ c.1=N6.arrowSource a then
        N6.arrowMatrix ℤ a (N6.part r.1 r.2) (N6.part c.1 c.2) else 0) := rfl
  rw [hg]
  by_cases H : r.1=N6.arrowTarget a ∧ c.1=N6.arrowSource a
  · simp only [N6.insert,N6.assemble,if_pos H]
    exact (congrFun (congrFun hb (N6.part r.1 r.2)) (N6.part c.1 c.2)).symm
  · simp only [N6.insert,N6.assemble,if_neg H,Matrix.zero_apply,Int.cast_zero]

variable {R : Type*} [CommRing R] (π : R) (ρ : R →+* k)
variable (h : RingParameters 6 R k π ρ)

theorem computation :
    ∃ φ : Data.case6.PathAlgebra k →ₐ[k] Data.case6.End k π ρ h,
      (∀ i, Data.case6.matrix π ρ h (φ (Data.quiver6.vertex k i)) = Data.case6.vertexMatrix k i) ∧
      (∀ a, Data.case6.matrix π ρ h (φ (Data.quiver6.arrow k a)) = Data.case6.arrowValue k a) ∧
      (∀ p ∈ Data.quiver6.ideal k, φ p = 0) ∧
      Function.Surjective φ ∧
      Module.Finite k (Data.case6.Presented k) ∧ Module.Finite k (Data.case6.End k π ρ h) ∧
      Module.finrank k (Data.case6.Presented k) = 1708 ∧
      Module.finrank k (Data.case6.End k π ρ h) = 1708 :=
  Dataset.transport Data.case6 π ρ h (N6.endAlgebra k) (image_eq π ρ h)
    (Presentation.pathMap k) (vertex_image k) (arrow_image k) (Presentation.relations_zero k)
    (Presentation.pathMap_surjective k) inferInstance (N6.endFinite k)
    (Presentation.presented_dimension k) (N6.end_finrank k)
end UniserialComputations.Uniform.Case6
