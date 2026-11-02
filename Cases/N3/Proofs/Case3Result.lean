import Case3Dataset
import Case3Bridge
import Case3Presentation
import UniformResult

noncomputable section
namespace UniserialComputations.Uniform.Case3
variable (k : Type*) [Field k]
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

lemma vertex_image (i : Fin 5) :
    (Presentation.pathMap k (Data.quiver3.vertex k i)).val = Data.case3.vertexMatrix k i := by
  rw [QuiverData.Representation.pathMap_vertex]
  change Matrix.single i i (1:k) = Matrix.diagonal (fun a => if coordinates.vertex a=i then 1 else 0)
  have hv : coordinates.vertex = (fun a : Fin 5 => a) := by decide
  rw [hv]
  ext a b
  simp only [Matrix.single_apply,Matrix.diagonal_apply]
  split_ifs <;> aesop
lemma arrow_image (a : Fin Data.quiver3.arrows) :
    (Presentation.pathMap k (Data.quiver3.arrow k a)).val = Data.case3.arrowValue k a := by
  rw [QuiverData.Representation.pathMap_arrow]
  change Matrix.single (Data.quiver3.target a) (Data.quiver3.source a) (1:k) = _
  ext r c
  simp [Dataset.arrowValue,Data.case3,Data.arrows3,Matrix.map_apply,Matrix.single_apply,apply_ite]

variable {R : Type*} [CommRing R] (π : R) (ρ : R →+* k)
variable (h : RingParameters 3 R k π ρ)

theorem computation :
    ∃ φ : Data.case3.PathAlgebra k →ₐ[k] Data.case3.End k π ρ h,
      (∀ i, Data.case3.matrix π ρ h (φ (Data.quiver3.vertex k i)) = Data.case3.vertexMatrix k i) ∧
      (∀ a, Data.case3.matrix π ρ h (φ (Data.quiver3.arrow k a)) = Data.case3.arrowValue k a) ∧
      (∀ p ∈ Data.quiver3.ideal k, φ p = 0) ∧
      Function.Surjective φ ∧
      Module.Finite k (Data.case3.Presented k) ∧ Module.Finite k (Data.case3.End k π ρ h) ∧
      Module.finrank k (Data.case3.Presented k) = 15 ∧
      Module.finrank k (Data.case3.End k π ρ h) = 15 :=
  Dataset.transport Data.case3 π ρ h (Chain.endAlgebra k 5) (image_eq π ρ h)
    (Presentation.pathMap k) (vertex_image k) (arrow_image k) (Presentation.relations_zero k)
    (Presentation.pathMap_surjective k) inferInstance inferInstance
    (Presentation.presented_dimension k) ((N3.C2_certificate k).2.2.2)
end UniserialComputations.Uniform.Case3
