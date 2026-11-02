import Case6RelationEquiv
noncomputable section
namespace UniserialComputations.Uniform.Case6.Presentation
open QuiverData
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
def presentedEquiv : Data.quiver6.Presented k ≃ₐ[k] N6.Presentation.Presented k :=
  presentationEquiv k (pathEquiv k) (Data.quiver6.Relations k) (N6.Presentation.Relations k)
    (relations_forward k) (relations_backward k)

instance : Module.Finite k (Data.quiver6.Presented k) := Module.Finite.of_surjective (presentedEquiv k).symm.toLinearMap (presentedEquiv k).symm.surjective
theorem presented_dimension : Module.finrank k (Data.quiver6.Presented k) = 1708 :=
  (presentedEquiv k).toLinearEquiv.finrank_eq.trans (N6.Presentation.presented_dimension k)

def pathMap : Data.quiver6.PathAlgebra k →ₐ[k] N6.End k := (N6.Presentation.pathMap k).comp (pathEquiv k).toAlgHom
theorem pathMap_surjective : Function.Surjective (pathMap k) :=
  (N6.Presentation.pathMap_surjective k).comp (pathEquiv k).surjective
@[simp] theorem pathMap_vertex (i : Fin 47) : pathMap k (Data.quiver6.vertex k i) = N6.vertex k i := by
  change N6.Presentation.pathMap k (pathEquiv k (Data.quiver6.vertex k i)) = _
  rw [pathEquiv_vertex]
  rfl
@[simp] theorem pathMap_arrow (b : Fin 75) : pathMap k (Data.quiver6.arrow k b) = N6.arrow k b := by
  change N6.Presentation.pathMap k (pathEquiv k (Data.quiver6.arrow k b)) = _
  rw [pathEquiv_arrow]
  rfl

theorem relations_zero (z : Fin Data.quiver6.relations.length) :
    pathMap k (Data.quiver6.polynomial (Data.quiver6.arrow k) Data.quiver6.relations[z])=0 := by
  have H := congrArg (N6.Presentation.evaluate k) (relations_forward k _ _ (QuiverData.Relations.relation (Q:=Data.quiver6) z))
  change N6.Presentation.pathMap k (pathEquiv k (Data.quiver6.polynomial (Data.quiver6.arrow k) Data.quiver6.relations[z])) =
    N6.Presentation.pathMap k (pathEquiv k 0) at H
  rw [map_zero,map_zero] at H
  exact H

end UniserialComputations.Uniform.Case6.Presentation
