import N6Relations
import Mathlib.Data.List.Induction
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination
noncomputable section
namespace UniserialComputations.N6
namespace Presentation
set_option maxHeartbeats 400000
set_option maxRecDepth 20000
variable (k : Type*) [Field k]
abbrev Generator := Fin 47 ⊕ Fin 75
abbrev Free := FreeAlgebra k Generator
def ev (v : Fin 47) : Free k := FreeAlgebra.ι k (Sum.inl v)
def ea (b : Fin 75) : Free k := FreeAlgebra.ι k (Sum.inr b)
inductive PathRelations : Free k → Free k → Prop
  | vv (i j : Fin 47) : PathRelations (ev k i*ev k j) (if i=j then ev k i else 0)
  | va (i : Fin 47) (b : Fin 75) : PathRelations (ev k i*ea k b) (if i=arrowTarget b then ea k b else 0)
  | av (b : Fin 75) (i : Fin 47) : PathRelations (ea k b*ev k i) (if i=arrowSource b then ea k b else 0)
  | unit : PathRelations (∑ i,ev k i) 1
/-- The ordinary unital path algebra, with the sum of the vertex idempotents as unit. -/
abbrev PathAlgebra := RingQuot (PathRelations k)
def pathVertex (v : Fin 47) : PathAlgebra k := RingQuot.mkAlgHom k (PathRelations k) (ev k v)
def pathArrow (b : Fin 75) : PathAlgebra k := RingQuot.mkAlgHom k (PathRelations k) (ea k b)
def word {A : Type*} [Monoid A] (a : Fin 75 → A) (p : List (Fin 75)) : A := (p.reverse.map a).prod
lemma word_append {A : Type*} [Monoid A] (a : Fin 75 → A) (p q : List (Fin 75)) : word a (p++q)=word a q*word a p := by
  simp [word,List.reverse_append,List.prod_append]
lemma word_snoc {A : Type*} [Monoid A] (a : Fin 75 → A) (p : List (Fin 75)) (b : Fin 75) : word a (p++[b])=a b*word a p := by
  simp [word_append,word]
def polynomial {A : Type*} [Ring A] (a : Fin 75 → A) (ts : List (Int × List (Fin 75))) : A := (ts.map (fun t => t.1 • word a t.2)).sum
inductive Relations : PathAlgebra k → PathAlgebra k → Prop
  | relation (z : Fin 47) : Relations (polynomial (pathArrow k) (relationTerms z)) 0
/-- The quotient by precisely the 47 supplied relations. -/
abbrev Presented := RingQuot (Relations k)
/-- Derive cancellation using the existing semiring operations. This avoids a
transparency diamond in typeclass search through the two nested RingQuot types. -/
instance presentedRightCancel : IsRightCancelAdd (Presented k) := by
  letI : Ring (Presented k) := Algebra.semiringToRing k
  infer_instance
def q : PathAlgebra k →ₐ[k] Presented k := RingQuot.mkAlgHom k (Relations k)
def e (v : Fin 47) : Presented k := q k (pathVertex k v)
def a (b : Fin 75) : Presented k := q k (pathArrow k b)
lemma relation_zero (z : Fin 47) : polynomial (a k) (relationTerms z)=0 := by
  have h := RingQuot.mkAlgHom_rel k (Relations.relation (k:=k) z)
  change q k (polynomial (pathArrow k) (relationTerms z))=q k 0 at h
  rw [map_zero] at h
  have he : q k (polynomial (pathArrow k) (relationTerms z))=polynomial (a k) (relationTerms z) := by
    simp only [polynomial,word,map_list_sum,map_zsmul,map_list_prod,List.map_map,Function.comp_def]
    rfl
  exact he ▸ h
lemma vv (i j : Fin 47) : e k i*e k j=if i=j then e k i else 0 := by
  have h := congrArg (q k) (RingQuot.mkAlgHom_rel k (PathRelations.vv (k:=k) i j))
  simpa only [e,pathVertex,map_mul,map_zero,apply_ite] using h
lemma va (i : Fin 47) (b : Fin 75) : e k i*a k b=if i=arrowTarget b then a k b else 0 := by
  have h := congrArg (q k) (RingQuot.mkAlgHom_rel k (PathRelations.va (k:=k) i b))
  simpa only [e,a,pathVertex,pathArrow,map_mul,map_zero,apply_ite] using h
lemma av (b : Fin 75) (i : Fin 47) : a k b*e k i=if i=arrowSource b then a k b else 0 := by
  have h := congrArg (q k) (RingQuot.mkAlgHom_rel k (PathRelations.av (k:=k) b i))
  simpa only [e,a,pathVertex,pathArrow,map_mul,map_zero,apply_ite] using h
lemma sum_e : ∑ i,e k i=1 := by
  have h := congrArg (q k) (RingQuot.mkAlgHom_rel k (PathRelations.unit (k:=k)))
  simpa only [e,pathVertex,map_sum,map_one] using h
/-- Anchoring at a source makes the empty path the correct vertex idempotent. -/
def walk (s : Fin 47) (p : List (Fin 75)) : Presented k := word (a k) p*e k s
lemma walk_snoc (s : Fin 47) (p : List (Fin 75)) (b : Fin 75) : walk k s (p++[b])=a k b*walk k s p := by
  simp only [walk,word_snoc,mul_assoc]
lemma word_cons (b : Fin 75) (p : List (Fin 75)) : word (a k) (b::p)=word (a k) p*a k b := by
  simpa [word] using word_append (a k) [b] p
lemma walkEnd_append (s : Fin 47) (p t : List (Fin 75)) :
    walkEnd s (p++t)=(walkEnd s p).bind (fun u => walkEnd u t) := by
  induction p generalizing s with
  | nil => rfl
  | cons b p ih => simp only [List.cons_append,walkEnd]; split_ifs <;> simp [ih]
lemma vertex_walk (i s t : Fin 47) (p : List (Fin 75)) (h : walkEnd s p=some t) :
    e k i*walk k s p=if i=t then walk k s p else 0 := by
  induction p using List.reverseRecOn generalizing t with
  | nil =>
    have ht : s=t := Option.some.inj h
    subst t
    by_cases hi : i=s
    · subst i; simpa [walk,word] using vv k s s
    · simpa [walk,word,hi] using vv k i s
  | append_singleton p b ih =>
    rw [walkEnd_append] at h
    cases hp : walkEnd s p with
    | none => simp [hp] at h
    | some u =>
      simp only [hp,Option.bind_some,walkEnd] at h
      split_ifs at h with hb
      · have ht : arrowTarget b=t := Option.some.inj h
        subst t
        rw [walk_snoc,← mul_assoc,va]
        split_ifs <;> simp
lemma arrow_incompatible (b : Fin 75) (s t : Fin 47) (p : List (Fin 75))
    (hp : walkEnd s p=some t) (h : arrowSource b≠t) : a k b*walk k s p=0 := by
  have hv := vertex_walk k t s t p hp
  rw [if_pos rfl] at hv
  rw [← hv,← mul_assoc,av,if_neg (Ne.symm h),zero_mul]
end Presentation
end UniserialComputations.N6
