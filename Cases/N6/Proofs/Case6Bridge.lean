import Case6Embedding
import Case6FreeCoordinates
import N6EndReduction

noncomputable section
namespace UniserialComputations.Uniform.Case6
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h : RingParameters 6 R k π ρ)

def toOld {i j} (f : Data.objects6.Hom π i j) : N6.HomData π i j where
  M := f.ambient
  U := f.source
  ambient_descent := f.ambient_descent
  source_descent := f.source_descent
  commutes := by
    intro r c
    have H := f.commutes r c
    rw [embedding_eq] at H
    exact H

def fromOld {i j} (f : N6.HomData π i j) : Data.objects6.Hom π i j where
  ambient := f.M
  source := f.U
  ambient_descent := f.ambient_descent
  source_descent := f.source_descent
  commutes := by rw [embedding_eq]; exact f.commutes

theorem reduce_eq (f : Data.objects6.EndRepresentatives π) :
    coordinates.reduce π ρ f =
      (N6.reduceFamily π ρ h.nilpotent h.top_annihilator (fun i j => toOld π (f i j))).val := by
  ext a b
  simp [FreeCoordinates.reduce, coordinates, N6.reduceFamily, N6.assemble,
    N6.reduceHom, N6.reduceMatrix, N6.part, Data.part6, N6.freeSlot, freeSlot, a.2.isLt, b.2.isLt, toOld]

include h in
theorem image_mem (f : Data.objects6.EndRepresentatives π) :
    coordinates.reduce π ρ f ∈ N6.endAlgebra k := by
  rw [reduce_eq π ρ h f]
  exact (N6.reduceFamily π ρ h.nilpotent h.top_annihilator (fun i j => toOld π (f i j))).property

include h in
theorem image_surjective (T : N6.End k) :
    ∃ f : Data.objects6.EndRepresentatives π, coordinates.reduce π ρ f = T.val := by
  obtain ⟨f,hf⟩ := N6.reduceFamily_surjective π ρ h.nilpotent h.top_annihilator h.residue_surjective T
  refine ⟨fun i j => fromOld π (f i j), ?_⟩
  rw [reduce_eq π ρ h]
  exact congrArg Subtype.val hf

include h in
theorem image_eq : coordinates.imageAlgebra π ρ h = N6.endAlgebra k := by
  ext M
  constructor
  · rintro ⟨f,rfl⟩
    exact image_mem π ρ h f
  · intro H
    exact image_surjective π ρ h ⟨M,H⟩

end UniserialComputations.Uniform.Case6
