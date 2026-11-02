import UniformSpanning
import Mathlib.Data.Matrix.Basis

noncomputable section
namespace UniserialComputations.Uniform.QuiverData
variable {v : Nat} (Q : QuiverData v) (k : Type*) [Field k]

def matrixRepresentation (S : Subalgebra k (Matrix (Fin v) (Fin v) k))
    (hv : ∀ i, Matrix.single i i 1 ∈ S)
    (ha : ∀ b, Matrix.single (Q.target b) (Q.source b) 1 ∈ S) : Q.Representation k S where
  vertex i := ⟨Matrix.single i i 1, hv i⟩
  arrow b := ⟨Matrix.single (Q.target b) (Q.source b) 1, ha b⟩
  vv := by
    intro i j
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, apply_ite, Subalgebra.coe_zero]
    split_ifs with h
    · subst j; simp
    · simp [Matrix.single_mul_single_of_ne, h]
  va := by
    intro i b
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, apply_ite, Subalgebra.coe_zero]
    split_ifs with h
    · subst i; simp
    · simp [Matrix.single_mul_single_of_ne, h]
  av := by
    intro b i
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, apply_ite, Subalgebra.coe_zero]
    split_ifs with h
    · subst i; simp
    · simp [Matrix.single_mul_single_of_ne, Ne.symm h]
  unit := by
    apply Subtype.ext
    change S.val (∑ i, ⟨Matrix.single i i (1:k), hv i⟩) = S.val 1
    rw [map_sum, map_one]
    exact Matrix.sum_single_one

namespace Representation
variable {Q k} {A : Type*} [Ring A] [Algebra k A] (r : Q.Representation k A)
  (hrel : ∀ z : Fin Q.relations.length, r.pathMap (Q.polynomial (Q.arrow k) Q.relations[z])=0)

def evaluate : Q.Presented k →ₐ[k] A := RingQuot.liftAlgHom k
  ⟨r.pathMap, by
    intro x y h
    cases h with
    | relation z => simpa only [map_zero] using hrel z⟩
@[simp] theorem evaluate_q (p : Q.PathAlgebra k) : r.evaluate hrel (Q.q k p) = r.pathMap p := rfl
include hrel in
theorem ideal_vanish : ∀ p ∈ Q.ideal k, r.pathMap p = 0 := by
  have H : Q.ideal k ≤ TwoSidedIdeal.ker r.pathMap := by
    apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨z,rfl⟩
    exact (TwoSidedIdeal.mem_ker _).mpr (hrel z)
  intro p hp
  exact (TwoSidedIdeal.mem_ker _).mp (H hp)

theorem pathMap_walk (s : Fin v) (p : List (Fin Q.arrows)) :
    r.pathMap (Q.word (Q.arrow k) p * Q.vertex k s) = Q.word r.arrow p * r.vertex s := by
  simp only [word, map_mul, map_list_prod, List.map_map, Function.comp_def,
    pathMap_vertex, pathMap_arrow]
theorem evaluate_walk (s : Fin v) (p : List (Fin Q.arrows)) :
    r.evaluate hrel (Q.walk k s p) = Q.word r.arrow p * r.vertex s := by
  have H : Q.walk k s p = Q.q k (Q.word (Q.arrow k) p * Q.vertex k s) := by
    simp only [walk,word,e,a,map_mul,map_list_prod,List.map_map,Function.comp_def]
    rfl
  rw [H,evaluate_q,r.pathMap_walk]

end Representation
end UniserialComputations.Uniform.QuiverData
