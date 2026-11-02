import N5Computations
import Mathlib.Algebra.RingQuot
noncomputable section
namespace UniserialComputations.N5
set_option maxHeartbeats 8000000
def arrowSource : Fin 23 → Fin 18 := ![0,1,2,3,4,6,7,8,9,10,11,11,12,13,13,14,14,15,16,16,17,17,17]
def arrowTarget : Fin 23 → Fin 18 := ![1,6,7,17,5,9,11,4,17,16,3,12,17,2,16,11,15,12,7,14,8,10,13]
def arrowRow : Fin 23 → Fin 19 := ![1,6,7,18,5,9,11,4,17,16,3,12,18,2,16,11,15,12,7,14,8,10,13]
def arrowCol : Fin 23 → Fin 19 := ![0,1,2,3,4,6,7,8,9,10,11,11,12,13,13,14,14,15,16,16,18,17,17]
def slotVertex (i : Fin 19) : Fin 18 := if h : i.val<18 then ⟨i.val,h⟩ else 17
theorem arrow_allowed : ∀ a, Allowed (arrowRow a) (arrowCol a) := by decide
theorem arrow_offdiag : ∀ a, arrowRow a≠arrowCol a := by decide
theorem arrow_endpoints : ∀ a, slotVertex (arrowRow a)=arrowTarget a ∧ slotVertex (arrowCol a)=arrowSource a := by decide
variable (k : Type*) [Field k]
def vertex (v : Fin 18) : End k := ⟨Matrix.diagonal (fun i => if slotVertex i=v then 1 else 0), by
  constructor
  · intro i j h
    have hij : i≠j := by rintro rfl; exact h (allowed_refl i)
    simp [Matrix.diagonal_apply_ne _ hij]
  · simp [slotVertex]⟩
def arrow (a : Fin 23) : End k := ⟨Matrix.single (arrowRow a) (arrowCol a) 1, by
  constructor
  · intro i j h
    simp only [Matrix.single_apply]
    split_ifs with hh
    · obtain ⟨rfl,rfl⟩ := hh; exact (h (arrow_allowed a)).elim
    · rfl
  · have hh := arrow_offdiag a
    simp only [Matrix.single_apply]
    split_ifs <;> simp_all⟩

theorem vertex_mul (i j : Fin 18) : vertex k i*vertex k j=if i=j then vertex k i else 0 := by
  apply Subtype.ext
  change Matrix.diagonal _*Matrix.diagonal _ = _
  rw [Matrix.diagonal_mul_diagonal]
  ext r c
  by_cases hi : i=j
  · subst j; simp [vertex,Matrix.diagonal_apply]; split_ifs <;> simp_all
  · simp [hi,vertex,Matrix.diagonal_apply]; aesop

theorem vertex_arrow (i : Fin 18) (a : Fin 23) :
    vertex k i*arrow k a=if i=arrowTarget a then arrow k a else 0 := by
  apply Subtype.ext
  simp only [apply_ite,Subalgebra.coe_mul,Subalgebra.coe_zero]
  split_ifs with h
  all_goals ext r c
  all_goals have he := (arrow_endpoints a).1
  all_goals simp [vertex,arrow,Matrix.diagonal_mul,Matrix.single_apply]
  all_goals try split_ifs
  all_goals (try simp_all [Matrix.single_apply]) <;> aesop

theorem arrow_vertex (a : Fin 23) (i : Fin 18) :
    arrow k a*vertex k i=if i=arrowSource a then arrow k a else 0 := by
  apply Subtype.ext
  simp only [apply_ite,Subalgebra.coe_mul,Subalgebra.coe_zero]
  split_ifs with h
  all_goals ext r c
  all_goals have he := (arrow_endpoints a).2
  all_goals simp [vertex,arrow,Matrix.mul_diagonal,Matrix.single_apply]
  all_goals try split_ifs
  all_goals (try simp_all [Matrix.single_apply]) <;> aesop

theorem vertex_sum : ∑ i, vertex k i=1 := by
  apply Subtype.ext
  ext r c
  change (∑ i, (vertex k i).val r c) = (1 : Mat k) r c
  simp [vertex,Matrix.diagonal_apply,Matrix.one_apply]

abbrev Generator := Fin 18 ⊕ Fin 23
abbrev Free := FreeAlgebra k Generator
def ev (i : Fin 18) : Free k := FreeAlgebra.ι k (Sum.inl i)
def ea (a : Fin 23) : Free k := FreeAlgebra.ι k (Sum.inr a)
def freeMap : Free k →ₐ[k] End k := FreeAlgebra.lift k (Sum.elim (vertex k) (arrow k))
inductive PathRelations : Free k → Free k → Prop
  | vv (i j) : PathRelations (ev k i*ev k j) (if i=j then ev k i else 0)
  | va (i a) : PathRelations (ev k i*ea k a) (if i=arrowTarget a then ea k a else 0)
  | av (a i) : PathRelations (ea k a*ev k i) (if i=arrowSource a then ea k a else 0)
  | unit : PathRelations (∑ i, ev k i) 1
abbrev PathAlgebra := RingQuot (PathRelations k)
lemma freeMap_respects {x y : Free k} (h : PathRelations k x y) : freeMap k x=freeMap k y := by
  cases h with
  | vv i j => simpa [freeMap,ev,apply_ite] using vertex_mul k i j
  | va i a => simpa [freeMap,ev,ea,apply_ite] using vertex_arrow k i a
  | av a i => simpa [freeMap,ev,ea,apply_ite] using arrow_vertex k a i
  | unit => simpa [freeMap,ev] using vertex_sum k
/-- Evaluation from the actual path algebra, with vertex idempotents included. -/
def pathMap : PathAlgebra k →ₐ[k] End k := RingQuot.liftAlgHom k ⟨freeMap k,fun _ _ h => freeMap_respects k h⟩
def pathVertex (v : Fin 18) : PathAlgebra k := RingQuot.mkAlgHom k (PathRelations k) (ev k v)
def pathArrow (a : Fin 23) : PathAlgebra k := RingQuot.mkAlgHom k (PathRelations k) (ea k a)
@[simp] theorem pathMap_vertex (v : Fin 18) : pathMap k (pathVertex k v)=vertex k v := by rfl
@[simp] theorem pathMap_arrow (a : Fin 23) : pathMap k (pathArrow k a)=arrow k a := by rfl
theorem zero_relation_0 : pathMap k (pathArrow k 21*pathArrow k 3)=0 := by
  simp only [map_mul,pathMap_arrow]
  apply Subtype.ext
  change Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k)=(0 : Mat k)
  norm_num [arrowRow,arrowCol,Matrix.single_mul_single_of_ne]
theorem zero_relation_1 : pathMap k (pathArrow k 22*pathArrow k 3)=0 := by
  simp only [map_mul,pathMap_arrow]
  apply Subtype.ext
  change Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k)=(0 : Mat k)
  norm_num [arrowRow,arrowCol,Matrix.single_mul_single_of_ne]
theorem zero_relation_2 : pathMap k (pathArrow k 20*pathArrow k 8)=0 := by
  simp only [map_mul,pathMap_arrow]
  apply Subtype.ext
  change Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k)=(0 : Mat k)
  norm_num [arrowRow,arrowCol,Matrix.single_mul_single_of_ne]
theorem zero_relation_3 : pathMap k (pathArrow k 21*pathArrow k 12)=0 := by
  simp only [map_mul,pathMap_arrow]
  apply Subtype.ext
  change Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k)=(0 : Mat k)
  norm_num [arrowRow,arrowCol,Matrix.single_mul_single_of_ne]
theorem zero_relation_4 : pathMap k (pathArrow k 22*pathArrow k 12)=0 := by
  simp only [map_mul,pathMap_arrow]
  apply Subtype.ext
  change Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k)=(0 : Mat k)
  norm_num [arrowRow,arrowCol,Matrix.single_mul_single_of_ne]
theorem commutativity_relation_0 : pathMap k (pathArrow k 3*pathArrow k 10)=pathMap k (pathArrow k 12*pathArrow k 11) := by
  simp only [map_mul,pathMap_arrow]
  apply Subtype.ext
  change (Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k) : Mat k)=Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k)
  simp [arrowRow,arrowCol,Matrix.single_mul_single_same]
theorem commutativity_relation_1 : pathMap k (pathArrow k 2*pathArrow k 13)=pathMap k (pathArrow k 18*pathArrow k 14) := by
  simp only [map_mul,pathMap_arrow]
  apply Subtype.ext
  change (Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k) : Mat k)=Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k)
  simp [arrowRow,arrowCol,Matrix.single_mul_single_same]
theorem commutativity_relation_2 : pathMap k (pathArrow k 11*pathArrow k 15)=pathMap k (pathArrow k 17*pathArrow k 16) := by
  simp only [map_mul,pathMap_arrow]
  apply Subtype.ext
  change (Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k) : Mat k)=Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k)
  simp [arrowRow,arrowCol,Matrix.single_mul_single_same]
theorem commutativity_relation_3 : pathMap k (pathArrow k 6*pathArrow k 18)=pathMap k (pathArrow k 15*pathArrow k 19) := by
  simp only [map_mul,pathMap_arrow]
  apply Subtype.ext
  change (Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k) : Mat k)=Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k)
  simp [arrowRow,arrowCol,Matrix.single_mul_single_same]
theorem commutativity_relation_4 : pathMap k (pathArrow k 9*pathArrow k 21)=pathMap k (pathArrow k 14*pathArrow k 22) := by
  simp only [map_mul,pathMap_arrow]
  apply Subtype.ext
  change (Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k) : Mat k)=Matrix.single _ _ (1:k)*Matrix.single _ _ (1:k)
  simp [arrowRow,arrowCol,Matrix.single_mul_single_same]
end UniserialComputations.N5
