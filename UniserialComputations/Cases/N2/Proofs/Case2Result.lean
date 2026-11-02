import Case2Dataset
import Case2Bridge
import Case2Presentation
import UniformResult

noncomputable section
namespace UniserialComputations.Uniform.Case2
variable (k : Type*) [Field k]
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

lemma vertex_image (i : Fin 3) :
    (Presentation.pathMap k (Data.quiver2.vertex k i)).val = Data.case2.vertexMatrix k i := by
  rw [QuiverData.Representation.pathMap_vertex]
  change Matrix.single i i (1:k) = Matrix.diagonal (fun a => if coordinates.vertex a=i then 1 else 0)
  have hv : coordinates.vertex = (fun a : Fin 3 => a) := by decide
  rw [hv]
  ext a b
  simp only [Matrix.single_apply,Matrix.diagonal_apply]
  split_ifs <;> aesop
lemma arrow_image (a : Fin Data.quiver2.arrows) :
    (Presentation.pathMap k (Data.quiver2.arrow k a)).val = Data.case2.arrowValue k a := by
  rw [QuiverData.Representation.pathMap_arrow]
  change Matrix.single (Data.quiver2.target a) (Data.quiver2.source a) (1:k) = _
  ext r c
  simp [Dataset.arrowValue,Data.case2,Data.arrows2,Matrix.map_apply,Matrix.single_apply,apply_ite]

variable {R : Type*} [CommRing R] (π : R) (ρ : R →+* k)
variable (h : RingParameters 2 R k π ρ)

theorem computation :
    ∃ φ : Data.case2.PathAlgebra k →ₐ[k] Data.case2.End k π ρ h,
      (∀ i, Data.case2.matrix π ρ h (φ (Data.quiver2.vertex k i)) = Data.case2.vertexMatrix k i) ∧
      (∀ a, Data.case2.matrix π ρ h (φ (Data.quiver2.arrow k a)) = Data.case2.arrowValue k a) ∧
      (∀ p ∈ Data.quiver2.ideal k, φ p = 0) ∧
      Function.Surjective φ ∧
      Module.Finite k (Data.case2.Presented k) ∧ Module.Finite k (Data.case2.End k π ρ h) ∧
      Module.finrank k (Data.case2.Presented k) = 6 ∧
      Module.finrank k (Data.case2.End k π ρ h) = 6 :=
  Dataset.transport Data.case2 π ρ h (N2.endAlgebra k) (image_eq π ρ h)
    (Presentation.pathMap k) (vertex_image k) (arrow_image k) (Presentation.relations_zero k)
    (Presentation.pathMap_surjective k) inferInstance inferInstance
    (Presentation.presented_dimension k) (N2.end_dimension k)
end UniserialComputations.Uniform.Case2
