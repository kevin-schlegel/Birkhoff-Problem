import Case4Dataset
import Case4Bridge
import Case4Presentation
import UniformResult

noncomputable section
namespace UniserialComputations.Uniform.Case4
variable (k : Type*) [Field k]
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

lemma vertex_image (i : Fin 9) :
    (Presentation.pathMap k (Data.quiver4.vertex k i)).val = Data.case4.vertexMatrix k i := by
  rw [QuiverData.Representation.pathMap_vertex]
  change Matrix.single i i (1:k) = Matrix.diagonal (fun a => if coordinates.vertex a=i then 1 else 0)
  have hv : coordinates.vertex = (fun a : Fin 9 => a) := by decide
  rw [hv]
  ext a b
  simp only [Matrix.single_apply,Matrix.diagonal_apply]
  split_ifs <;> aesop
lemma arrow_image (a : Fin Data.quiver4.arrows) :
    (Presentation.pathMap k (Data.quiver4.arrow k a)).val = Data.case4.arrowValue k a := by
  rw [QuiverData.Representation.pathMap_arrow]
  change Matrix.single (Data.quiver4.target a) (Data.quiver4.source a) (1:k) = _
  ext r c
  simp [Dataset.arrowValue,Data.case4,Data.arrows4,Matrix.map_apply,Matrix.single_apply,apply_ite]

variable {R : Type*} [CommRing R] (π : R) (ρ : R →+* k)
variable (h : RingParameters 4 R k π ρ)

theorem computation :
    ∃ φ : Data.case4.PathAlgebra k →ₐ[k] Data.case4.End k π ρ h,
      (∀ i, Data.case4.matrix π ρ h (φ (Data.quiver4.vertex k i)) = Data.case4.vertexMatrix k i) ∧
      (∀ a, Data.case4.matrix π ρ h (φ (Data.quiver4.arrow k a)) = Data.case4.arrowValue k a) ∧
      (∀ p ∈ Data.quiver4.ideal k, φ p = 0) ∧
      Function.Surjective φ ∧
      Module.Finite k (Data.case4.Presented k) ∧ Module.Finite k (Data.case4.End k π ρ h) ∧
      Module.finrank k (Data.case4.Presented k) = 44 ∧
      Module.finrank k (Data.case4.End k π ρ h) = 44 :=
  Dataset.transport Data.case4 π ρ h (N4.endAlgebra k) (image_eq π ρ h)
    (Presentation.pathMap k) (vertex_image k) (arrow_image k) (Presentation.relations_zero k)
    (Presentation.pathMap_surjective k) inferInstance inferInstance
    (Presentation.presented_dimension k) (N4.end_dimension k)
end UniserialComputations.Uniform.Case4
