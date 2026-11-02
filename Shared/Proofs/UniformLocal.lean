import UniformQuotient
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.RingTheory.LocalRing.RingHom.Basic

noncomputable section
namespace UniserialComputations.Uniform
namespace ObjectFamily
/-- The single listed object at index `i`, with exactly the same matrices. -/
abbrev singleObject (D : ObjectFamily) (i : Fin D.vertices) : ObjectFamily where
  length := D.length
  vertices := 1
  ambientSlots := D.ambientSlots
  sourceSlots := D.sourceSlots
  labels := fun _ => D.labels i
  ambientLength := fun _ => D.ambientLength i
  sourceLength := fun _ => D.sourceLength i
  entry := fun _ => D.entry i
  ambientBound := fun _ => D.ambientBound i
  sourceBound := fun _ => D.sourceBound i
end ObjectFamily

variable {D : ObjectFamily} (C : FreeCoordinates D (Fin 1))
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters D.length R k π ρ)

theorem one_free_image : C.imageAlgebra π ρ h = ⊤ := by
  apply top_unique
  intro M _
  have hm : M = algebraMap k (Matrix (Fin 1) (Fin 1) k) (M 0 0) := by
    ext a b
    fin_cases a <;> fin_cases b
    simp [Matrix.algebraMap_matrix_apply]
  rw [hm]
  exact (C.imageAlgebra π ρ h).algebraMap_mem _

def matrixOneEquiv (k : Type*) [Field k] : Matrix (Fin 1) (Fin 1) k ≃ₐ[k] k where
  toFun M := M 0 0
  invFun x := fun _ _ => x
  left_inv M := by ext a b; fin_cases a <;> fin_cases b; rfl
  right_inv x := rfl
  map_mul' A B := by simp [Matrix.mul_apply]
  map_add' A B := rfl
  commutes' x := by simp [Matrix.algebraMap_matrix_apply]

/-- With one free ambient coordinate, the prescribed quotient endomorphism
algebra is the residue field. -/
def oneFreeEquiv : EndAlgebra C π ρ h ≃ₐ[k] k :=
  (EndAlgebra.imageAlgEquiv C π ρ h).trans
    ((Subalgebra.equivOfEq _ _ (one_free_image C π ρ h)).trans
      ((Subalgebra.topEquiv : (⊤ : Subalgebra k (Matrix (Fin 1) (Fin 1) k)) ≃ₐ[k] _).trans
        (matrixOneEquiv k)))

theorem oneFree_local : IsLocalRing (EndAlgebra C π ρ h) :=
  (oneFreeEquiv C π ρ h).symm.toRingEquiv.isLocalRing
end UniserialComputations.Uniform
