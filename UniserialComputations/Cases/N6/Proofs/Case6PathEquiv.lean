import Case6Quiver
import UniformPresentationEquiv
import UniformMatrixPaths
import N6Certificate

noncomputable section
namespace UniserialComputations.Uniform.Case6.Presentation
open QuiverData
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]

def pathEquiv : Data.quiver6.PathAlgebra k ≃ₐ[k] N6.Presentation.PathAlgebra k :=
  presentationEquiv k ((AlgEquiv.refl : Data.quiver6.Free k ≃ₐ[k] Data.quiver6.Free k)) (Data.quiver6.PathRelations k) (N6.Presentation.PathRelations k)
    (by
      intro x y H
      cases H with
      | vv i j => exact RingQuot.mkAlgHom_rel k (N6.Presentation.PathRelations.vv i j)
      | va i b => exact RingQuot.mkAlgHom_rel k (N6.Presentation.PathRelations.va i b)
      | av b i => exact RingQuot.mkAlgHom_rel k (N6.Presentation.PathRelations.av b i)
      | unit => exact RingQuot.mkAlgHom_rel k (N6.Presentation.PathRelations.unit))
    (by
      intro x y H
      cases H with
      | vv i j => exact RingQuot.mkAlgHom_rel k (QuiverData.PathRelations.vv (Q:=Data.quiver6) i j)
      | va i b => exact RingQuot.mkAlgHom_rel k (QuiverData.PathRelations.va (Q:=Data.quiver6) i b)
      | av b i => exact RingQuot.mkAlgHom_rel k (QuiverData.PathRelations.av (Q:=Data.quiver6) b i)
      | unit => exact RingQuot.mkAlgHom_rel k (QuiverData.PathRelations.unit (Q:=Data.quiver6)))

@[simp] lemma pathEquiv_vertex (i : Fin 47) : pathEquiv k (Data.quiver6.vertex k i) = N6.Presentation.pathVertex k i := rfl
@[simp] lemma pathEquiv_arrow (b : Fin 75) : pathEquiv k (Data.quiver6.arrow k b) = N6.Presentation.pathArrow k b := rfl
@[simp] lemma pathEquiv_symm_vertex (i : Fin 47) : (pathEquiv k).symm (N6.Presentation.pathVertex k i) = Data.quiver6.vertex k i := rfl
@[simp] lemma pathEquiv_symm_arrow (b : Fin 75) : (pathEquiv k).symm (N6.Presentation.pathArrow k b) = Data.quiver6.arrow k b := rfl

end UniserialComputations.Uniform.Case6.Presentation
