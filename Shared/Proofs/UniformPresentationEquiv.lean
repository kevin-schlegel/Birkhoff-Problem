import UniformPaths

noncomputable section
namespace UniserialComputations.Uniform
variable (k : Type*) [Field k]
variable {A B : Type*} [Ring A] [Ring B] [Algebra k A] [Algebra k B]

/-- Transport a presentation along an algebra equivalence, proving both
directions respect the specified generating relations. -/
def presentationEquiv (e : A ≃ₐ[k] B) (r : A → A → Prop) (s : B → B → Prop)
    (h : ∀ x y, r x y → RingQuot.mkAlgHom k s (e x) = RingQuot.mkAlgHom k s (e y))
    (g : ∀ x y, s x y → RingQuot.mkAlgHom k r (e.symm x) = RingQuot.mkAlgHom k r (e.symm y)) :
    RingQuot r ≃ₐ[k] RingQuot s :=
  AlgEquiv.ofAlgHom
    (RingQuot.liftAlgHom k ⟨(RingQuot.mkAlgHom k s).comp e.toAlgHom, h⟩)
    (RingQuot.liftAlgHom k ⟨(RingQuot.mkAlgHom k r).comp e.symm.toAlgHom, g⟩)
    (by
      apply RingQuot.ringQuot_ext'
      ext a
      change RingQuot.mkAlgHom k s (e (e.symm a)) = RingQuot.mkAlgHom k s a
      rw [e.apply_symm_apply])
    (by
      apply RingQuot.ringQuot_ext'
      ext a
      change RingQuot.mkAlgHom k r (e.symm (e a)) = RingQuot.mkAlgHom k r a
      rw [e.symm_apply_apply])

@[simp] theorem presentationEquiv_mk (e : A ≃ₐ[k] B) (r : A → A → Prop) (s : B → B → Prop)
    (h : ∀ x y, r x y → RingQuot.mkAlgHom k s (e x) = RingQuot.mkAlgHom k s (e y))
    (g : ∀ x y, s x y → RingQuot.mkAlgHom k r (e.symm x) = RingQuot.mkAlgHom k r (e.symm y)) (a : A) :
    presentationEquiv k e r s h g (RingQuot.mkAlgHom k r a) = RingQuot.mkAlgHom k s (e a) := rfl

namespace QuiverData
variable {v : Nat} (Q : QuiverData v)
lemma map_word (f : A →ₐ[k] B) (a : Fin Q.arrows → A) (p : List (Fin Q.arrows)) :
    f (Q.word a p) = Q.word (fun b => f (a b)) p := by
  simp only [word,map_list_prod,List.map_map,Function.comp_def]
lemma map_polynomial (f : A →ₐ[k] B) (a : Fin Q.arrows → A)
    (terms : List (Int × List (Fin Q.arrows))) :
    f (Q.polynomial a terms) = Q.polynomial (fun b => f (a b)) terms := by
  simp only [polynomial,map_list_sum,List.map_map,Function.comp_def,map_zsmul,map_word]
end QuiverData
end UniserialComputations.Uniform
