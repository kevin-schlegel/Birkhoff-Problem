import UniformDataset
import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable section
namespace UniserialComputations.Uniform
namespace Dataset
variable (D : Dataset) {R k : Type*} [CommRing R] [Field k]
  (π : R) (ρ : R →+* k) (h : RingParameters D.objects.length R k π ρ)
/-- Faithful free-coordinate matrix of a class in the annihilation quotient. -/
def matrix : D.End k π ρ h →ₐ[k] Matrix D.Slot D.Slot k :=
  (D.coordinates.imageAlgebra π ρ h).val.comp
    (EndAlgebra.imageAlgEquiv D.coordinates π ρ h).toAlgHom

def modelEquiv (S : Subalgebra k (Matrix D.Slot D.Slot k))
    (he : D.coordinates.imageAlgebra π ρ h = S) : D.End k π ρ h ≃ₐ[k] S :=
  (EndAlgebra.imageAlgEquiv D.coordinates π ρ h).trans (Subalgebra.equivOfEq _ _ he)

lemma model_matrix (S : Subalgebra k (Matrix D.Slot D.Slot k))
    (he : D.coordinates.imageAlgebra π ρ h = S) (x : S) :
    D.matrix π ρ h ((D.modelEquiv π ρ h S he).symm x) = x.val := by
  have hh := (D.modelEquiv π ρ h S he).apply_symm_apply x
  exact congrArg Subtype.val hh

/-- Internal transport of a verified matrix presentation to the actual object quotient. -/
theorem transport (S : Subalgebra k (Matrix D.Slot D.Slot k))
    (he : D.coordinates.imageAlgebra π ρ h = S)
    (ψ : D.PathAlgebra k →ₐ[k] S)
    (hv : ∀ i, (ψ (D.quiver.vertex k i)).val = D.vertexMatrix k i)
    (ha : ∀ a, (ψ (D.quiver.arrow k a)).val = D.arrowValue k a)
    (hr : ∀ z : Fin D.quiver.relations.length,
      ψ (D.quiver.polynomial (D.quiver.arrow k) D.quiver.relations[z]) = 0)
    (hs : Function.Surjective ψ)
    (hpfin : Module.Finite k (D.Presented k)) (hefin : Module.Finite k S)
    (hpdim : Module.finrank k (D.Presented k) = D.dimension)
    (hedim : Module.finrank k S = D.dimension) :
    ∃ φ : D.PathAlgebra k →ₐ[k] D.End k π ρ h,
      (∀ i, D.matrix π ρ h (φ (D.quiver.vertex k i)) = D.vertexMatrix k i) ∧
      (∀ a, D.matrix π ρ h (φ (D.quiver.arrow k a)) = D.arrowValue k a) ∧
      (∀ p ∈ D.quiver.ideal k, φ p = 0) ∧
      Function.Surjective φ ∧
      Module.Finite k (D.Presented k) ∧ Module.Finite k (D.End k π ρ h) ∧
      Module.finrank k (D.Presented k) = D.dimension ∧
      Module.finrank k (D.End k π ρ h) = D.dimension := by
  let e := D.modelEquiv π ρ h S he
  let φ := e.symm.toAlgHom.comp ψ
  have hmatrix (x) : D.matrix π ρ h (φ x) = (ψ x).val := D.model_matrix π ρ h S he (ψ x)
  refine ⟨φ, (fun i => (hmatrix _).trans (hv i)), (fun a => (hmatrix _).trans (ha a)), ?_,
    e.symm.surjective.comp hs, hpfin, ?_, hpdim, ?_⟩
  · have HH : D.quiver.ideal k ≤ TwoSidedIdeal.ker ψ := by
      apply TwoSidedIdeal.span_le.mpr
      rintro _ ⟨z,rfl⟩
      exact (TwoSidedIdeal.mem_ker _).mpr (hr z)
    intro p hp
    change e.symm (ψ p) = 0
    rw [(TwoSidedIdeal.mem_ker _).mp (HH hp),map_zero]
  · letI := hefin
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  · exact e.toLinearEquiv.finrank_eq.trans hedim
end Dataset
end UniserialComputations.Uniform
