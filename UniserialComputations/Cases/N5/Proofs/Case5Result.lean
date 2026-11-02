import Case5Dataset
import Case5Bridge
import Case5Presentation
import UniformResult

noncomputable section
namespace UniserialComputations.Uniform.Case5
variable (k : Type*) [Field k]
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

lemma vertex_image (i : Fin 18) :
    (Presentation.pathMap k (Data.quiver5.vertex k i)).val = Data.case5.vertexMatrix k i := by
  rw [Presentation.pathMap_vertex]
  have hv : coordinates.vertex = N5.slotVertex := by decide
  change Matrix.diagonal _ = Matrix.diagonal _
  rw [hv]
lemma arrow_image (a : Fin Data.quiver5.arrows) :
    (Presentation.pathMap k (Data.quiver5.arrow k a)).val = Data.case5.arrowValue k a := by
  rw [Presentation.pathMap_arrow]
  ext r c
  simp [N5.arrow,Dataset.arrowValue,Data.case5,Data.arrows5,Data.arrowRow5,Data.arrowCol5,N5.arrowRow,N5.arrowCol,Matrix.map_apply,Matrix.single_apply,apply_ite]

variable {R : Type*} [CommRing R] (π : R) (ρ : R →+* k)
variable (h : RingParameters 5 R k π ρ)

theorem computation :
    ∃ φ : Data.case5.PathAlgebra k →ₐ[k] Data.case5.End k π ρ h,
      (∀ i, Data.case5.matrix π ρ h (φ (Data.quiver5.vertex k i)) = Data.case5.vertexMatrix k i) ∧
      (∀ a, Data.case5.matrix π ρ h (φ (Data.quiver5.arrow k a)) = Data.case5.arrowValue k a) ∧
      (∀ p ∈ Data.quiver5.ideal k, φ p = 0) ∧
      Function.Surjective φ ∧
      Module.Finite k (Data.case5.Presented k) ∧ Module.Finite k (Data.case5.End k π ρ h) ∧
      Module.finrank k (Data.case5.Presented k) = 179 ∧
      Module.finrank k (Data.case5.End k π ρ h) = 179 :=
  Dataset.transport Data.case5 π ρ h (N5.endAlgebra k) (image_eq π ρ h)
    (Presentation.pathMap k) (vertex_image k) (arrow_image k) (Presentation.relations_zero k)
    (Presentation.pathMap_surjective k) inferInstance inferInstance
    (Presentation.presented_dimension k) (N5.end_dimension k)
end UniserialComputations.Uniform.Case5
