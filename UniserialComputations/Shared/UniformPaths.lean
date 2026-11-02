import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Tactic

noncomputable section
namespace UniserialComputations.Uniform

/-- A finite quiver with a finite list of signed path relations.
Paths list arrows in traversal order; multiplication is composition. -/
structure QuiverData (vertices : Nat) where
  arrows : Nat
  source : Fin arrows → Fin vertices
  target : Fin arrows → Fin vertices
  relations : List (List (Int × List (Fin arrows)))

namespace QuiverData
variable {v : Nat} (Q : QuiverData v) (k : Type*) [Field k]
abbrev Free := FreeAlgebra k (Fin v ⊕ Fin Q.arrows)
def ev (i : Fin v) : Q.Free k := FreeAlgebra.ι k (Sum.inl i)
def ea (a : Fin Q.arrows) : Q.Free k := FreeAlgebra.ι k (Sum.inr a)

inductive PathRelations : Q.Free k → Q.Free k → Prop
  | vv (i j) : PathRelations (Q.ev k i * Q.ev k j) (if i=j then Q.ev k i else 0)
  | va (i a) : PathRelations (Q.ev k i * Q.ea k a) (if i=Q.target a then Q.ea k a else 0)
  | av (a i) : PathRelations (Q.ea k a * Q.ev k i) (if i=Q.source a then Q.ea k a else 0)
  | unit : PathRelations (∑ i, Q.ev k i) 1

abbrev PathAlgebra := RingQuot (Q.PathRelations k)
def vertex (i : Fin v) : Q.PathAlgebra k := RingQuot.mkAlgHom k (Q.PathRelations k) (Q.ev k i)
def arrow (a : Fin Q.arrows) : Q.PathAlgebra k := RingQuot.mkAlgHom k (Q.PathRelations k) (Q.ea k a)

def word {A : Type*} [Monoid A] (a : Fin Q.arrows → A) (p : List (Fin Q.arrows)) : A :=
  (p.reverse.map a).prod
def polynomial {A : Type*} [Ring A] (a : Fin Q.arrows → A)
    (terms : List (Int × List (Fin Q.arrows))) : A :=
  (terms.map (fun t => t.1 • Q.word a t.2)).sum

inductive Relations : Q.PathAlgebra k → Q.PathAlgebra k → Prop
  | relation (z : Fin Q.relations.length) :
      Relations (Q.polynomial (Q.arrow k) (Q.relations[z])) 0
abbrev Presented := RingQuot (Q.Relations k)
instance : IsRightCancelAdd (Q.Presented k) := by
  letI : Ring (Q.Presented k) := Algebra.semiringToRing k
  infer_instance

def ideal : TwoSidedIdeal (Q.PathAlgebra k) :=
  TwoSidedIdeal.span (Set.range (fun z : Fin Q.relations.length => Q.polynomial (Q.arrow k) Q.relations[z]))
def q : Q.PathAlgebra k →ₐ[k] Q.Presented k := RingQuot.mkAlgHom k (Q.Relations k)
def e (i : Fin v) : Q.Presented k := Q.q k (Q.vertex k i)
def a (b : Fin Q.arrows) : Q.Presented k := Q.q k (Q.arrow k b)

lemma vertex_mul (i j) : Q.vertex k i * Q.vertex k j = if i=j then Q.vertex k i else 0 := by
  simpa only [vertex, map_mul, apply_ite, map_zero] using RingQuot.mkAlgHom_rel k (PathRelations.vv (Q:=Q) (k:=k) i j)
lemma vertex_arrow (i b) : Q.vertex k i * Q.arrow k b = if i=Q.target b then Q.arrow k b else 0 := by
  simpa only [vertex, arrow, map_mul, apply_ite, map_zero] using RingQuot.mkAlgHom_rel k (PathRelations.va (Q:=Q) (k:=k) i b)
lemma arrow_vertex (b i) : Q.arrow k b * Q.vertex k i = if i=Q.source b then Q.arrow k b else 0 := by
  simpa only [vertex, arrow, map_mul, apply_ite, map_zero] using RingQuot.mkAlgHom_rel k (PathRelations.av (Q:=Q) (k:=k) b i)
lemma sum_vertex : (∑ i, Q.vertex k i) = 1 := by
  simpa only [vertex, map_sum, map_one] using RingQuot.mkAlgHom_rel k (PathRelations.unit (Q:=Q) (k:=k))

lemma vv (i j) : Q.e k i * Q.e k j = if i=j then Q.e k i else 0 := by
  simpa only [e, map_mul, apply_ite, map_zero] using congrArg (Q.q k) (Q.vertex_mul k i j)
lemma va (i b) : Q.e k i * Q.a k b = if i=Q.target b then Q.a k b else 0 := by
  simpa only [e, a, map_mul, apply_ite, map_zero] using congrArg (Q.q k) (Q.vertex_arrow k i b)
lemma av (b i) : Q.a k b * Q.e k i = if i=Q.source b then Q.a k b else 0 := by
  simpa only [e, a, map_mul, apply_ite, map_zero] using congrArg (Q.q k) (Q.arrow_vertex k b i)
lemma sum_e : (∑ i, Q.e k i) = 1 := by
  simpa only [e, map_sum, map_one] using congrArg (Q.q k) (Q.sum_vertex k)

lemma relation_zero (z : Fin Q.relations.length) : Q.polynomial (Q.a k) Q.relations[z] = 0 := by
  have H := RingQuot.mkAlgHom_rel k (Relations.relation (Q:=Q) (k:=k) z)
  change Q.q k (Q.polynomial (Q.arrow k) Q.relations[z]) = Q.q k 0 at H
  rw [map_zero] at H
  have he : Q.q k (Q.polynomial (Q.arrow k) Q.relations[z]) =
      Q.polynomial (Q.a k) Q.relations[z] := by
    simp only [polynomial, word, map_list_sum, map_zsmul, map_list_prod,
      List.map_map, Function.comp_def]
    rfl
  exact he ▸ H

structure Representation (A : Type*) [Ring A] [Algebra k A] where
  vertex : Fin v → A
  arrow : Fin Q.arrows → A
  vv : ∀ i j, vertex i * vertex j = if i=j then vertex i else 0
  va : ∀ i b, vertex i * arrow b = if i=Q.target b then arrow b else 0
  av : ∀ b i, arrow b * vertex i = if i=Q.source b then arrow b else 0
  unit : ∑ i, vertex i = 1

namespace Representation
variable {Q k} {A : Type*} [Ring A] [Algebra k A] (r : Q.Representation k A)
def freeMap : Q.Free k →ₐ[k] A := FreeAlgebra.lift k (Sum.elim r.vertex r.arrow)
lemma respects {x y} (h : Q.PathRelations k x y) : r.freeMap x = r.freeMap y := by
  cases h with
  | vv i j => simpa [freeMap,ev,apply_ite] using r.vv i j
  | va i b => simpa [freeMap,ev,ea,apply_ite] using r.va i b
  | av b i => simpa [freeMap,ev,ea,apply_ite] using r.av b i
  | unit => simpa [freeMap,ev] using r.unit
def pathMap : Q.PathAlgebra k →ₐ[k] A :=
  RingQuot.liftAlgHom k ⟨r.freeMap, fun _ _ h => r.respects h⟩
@[simp] lemma pathMap_vertex (i) : r.pathMap (Q.vertex k i) = r.vertex i := rfl
@[simp] lemma pathMap_arrow (b) : r.pathMap (Q.arrow k b) = r.arrow b := rfl
end Representation

@[ext] theorem hom_ext {A : Type*} [Ring A] [Algebra k A]
    (f g : Q.PathAlgebra k →ₐ[k] A)
    (hv : ∀ i, f (Q.vertex k i) = g (Q.vertex k i))
    (ha : ∀ b, f (Q.arrow k b) = g (Q.arrow k b)) : f=g := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext x
  cases x with
  | inl i => exact hv i
  | inr b => exact ha b

lemma word_append {A : Type*} [Monoid A] (a : Fin Q.arrows → A) (p q) :
    Q.word a (p++q) = Q.word a q * Q.word a p := by
  simp [word, List.reverse_append, List.prod_append]
def walk (s : Fin v) (p : List (Fin Q.arrows)) : Q.Presented k := Q.word (Q.a k) p * Q.e k s
lemma walk_snoc (s p b) : Q.walk k s (p++[b]) = Q.a k b * Q.walk k s p := by
  simp [walk, word_append, word, mul_assoc]
def walkEnd (s : Fin v) : List (Fin Q.arrows) → Option (Fin v)
  | [] => some s
  | b::p => if Q.source b = s then walkEnd (Q.target b) p else none

end QuiverData
end UniserialComputations.Uniform
