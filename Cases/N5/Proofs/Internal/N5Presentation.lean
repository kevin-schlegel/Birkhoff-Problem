import N5Paths
noncomputable section
namespace UniserialComputations.N5
namespace Presentation
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
variable (k : Type*) [Field k]
def zeroPairs : Fin 5 → Fin 23 × Fin 23 := ![(3,21),(3,22),(8,20),(12,21),(12,22)]
def commutePairs : Fin 5 → (Fin 23 × Fin 23) × (Fin 23 × Fin 23) := ![((10,3),(11,12)),((13,2),(14,18)),((15,11),(16,17)),((18,6),(19,15)),((21,9),(22,14))]
inductive Relations : PathAlgebra k → PathAlgebra k → Prop
  | zero (z : Fin 5) : Relations (pathArrow k (zeroPairs z).2*pathArrow k (zeroPairs z).1) 0
  | commute (z : Fin 5) : Relations
      (pathArrow k (commutePairs z).1.2*pathArrow k (commutePairs z).1.1)
      (pathArrow k (commutePairs z).2.2*pathArrow k (commutePairs z).2.1)
abbrev Presented := RingQuot (Relations k)
def q : PathAlgebra k →ₐ[k] Presented k := RingQuot.mkAlgHom k (Relations k)
def e (v : Fin 18) : Presented k := q k (pathVertex k v)
def a (v : Fin 23) : Presented k := q k (pathArrow k v)
lemma respects {x y} (h : Relations k x y) : pathMap k x=pathMap k y := by
  cases h with
  | zero z => simp only [map_zero]; fin_cases z
              all_goals first | exact zero_relation_0 k | exact zero_relation_1 k | exact zero_relation_2 k | exact zero_relation_3 k | exact zero_relation_4 k
  | commute z => fin_cases z
                 all_goals first | exact commutativity_relation_0 k | exact commutativity_relation_1 k | exact commutativity_relation_2 k | exact commutativity_relation_3 k | exact commutativity_relation_4 k
def evaluate : Presented k →ₐ[k] End k := RingQuot.liftAlgHom k ⟨pathMap k,fun _ _ h => respects k h⟩
lemma zero_rel (z : Fin 5) : a k (zeroPairs z).2*a k (zeroPairs z).1=0 := by
  simpa only [a,q,map_mul,map_zero] using (RingQuot.mkAlgHom_rel k (Relations.zero (k:=k) z))
lemma commute_rel (z : Fin 5) : a k (commutePairs z).1.2*a k (commutePairs z).1.1 = a k (commutePairs z).2.2*a k (commutePairs z).2.1 := by
  exact RingQuot.mkAlgHom_rel k (Relations.commute (k:=k) z)
lemma vv (i j : Fin 18) : e k i*e k j=if i=j then e k i else 0 := by
  have h := RingQuot.mkAlgHom_rel k (PathRelations.vv (k:=k) i j)
  have hh := congrArg (q k) h
  simpa only [e,a,pathVertex,pathArrow,map_mul,map_zero,apply_ite] using hh
lemma va (i : Fin 18) (b : Fin 23) : e k i*a k b=if i=arrowTarget b then a k b else 0 := by
  have h := RingQuot.mkAlgHom_rel k (PathRelations.va (k:=k) i b)
  have hh := congrArg (q k) h
  simpa only [e,a,pathVertex,pathArrow,map_mul,map_zero,apply_ite] using hh
lemma av (b : Fin 23) (i : Fin 18) : a k b*e k i=if i=arrowSource b then a k b else 0 := by
  have h := RingQuot.mkAlgHom_rel k (PathRelations.av (k:=k) b i)
  have hh := congrArg (q k) h
  simpa only [e,a,pathVertex,pathArrow,map_mul,map_zero,apply_ite] using hh
lemma sum_e : ∑ i, e k i=1 := by
  have h := RingQuot.mkAlgHom_rel k (PathRelations.unit (k:=k))
  have hh := congrArg (q k) h
  simpa only [e,pathVertex,map_sum,map_one] using hh

def normalRep (c : Coord) : Presented k := if c.val.1=c.val.2 then e k (slotVertex c.val.1) else wordValue (a k) (normalWord c.val.1 c.val.2)
lemma normalRep_eq (c : Coord) : normalRep k c=q k (representative k c) := by
  by_cases h : c.val.1=c.val.2
  · simp only [normalRep,representative,if_pos h,e]
  · simp only [normalRep,representative,if_neg h,wordValue,map_list_prod,List.map_map]
    rfl
lemma word_append {A : Type*} [Monoid A] (v : Fin 23 → A) (p q : List (Fin 23)) :
    wordValue v (p++q)=wordValue v q*wordValue v p := by
  simp [wordValue,List.reverse_append,List.prod_append]
lemma word_snoc {A : Type*} [Monoid A] (v : Fin 23 → A) (p : List (Fin 23)) (b : Fin 23) :
    wordValue v (p++[b])=v b*wordValue v p := by
  rw [word_append]
  simp only [wordValue,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
lemma context_commute (z : Fin 5) (p t : List (Fin 23)) :
    wordValue (a k) (p++[(commutePairs z).1.1,(commutePairs z).1.2]++t) =
    wordValue (a k) (p++[(commutePairs z).2.1,(commutePairs z).2.2]++t) := by
  simp only [word_append]
  simp only [wordValue,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  rw [commute_rel]
lemma context_zero (z : Fin 5) (p t : List (Fin 23)) :
    wordValue (a k) (p++[(zeroPairs z).1,(zeroPairs z).2]++t)=0 := by
  simp only [word_append]
  simp only [wordValue,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  rw [zero_rel,zero_mul,mul_zero]
lemma extend_0_0 : a k 0*normalRep k ⟨(0,0),by decide⟩=normalRep k ⟨(1,0),by decide⟩ := by
  change a k 0*e k 0=a k 0*1
  rw [av]
  norm_num [arrowSource]

lemma extend_1_1 : a k 1*normalRep k ⟨(1,0),by decide⟩=normalRep k ⟨(6,0),by decide⟩ := by
  change a k 1*wordValue (a k) [0] = wordValue (a k) [0, 1]
  rw [show a k 1*wordValue (a k) [0]=wordValue (a k) [0, 1] from (word_snoc (a k) [0] 1).symm]
  all_goals rfl
lemma extend_2_1 : a k 1*normalRep k ⟨(1,1),by decide⟩=normalRep k ⟨(6,1),by decide⟩ := by
  change a k 1*e k 1=a k 1*1
  rw [av]
  norm_num [arrowSource]

lemma extend_3_2 : a k 2*normalRep k ⟨(2,0),by decide⟩=normalRep k ⟨(7,0),by decide⟩ := by
  change a k 2*wordValue (a k) [0, 1, 5, 8, 22, 13] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18]
  rw [show a k 2*wordValue (a k) [0, 1, 5, 8, 22, 13]=wordValue (a k) [0, 1, 5, 8, 22, 13, 2] from (word_snoc (a k) [0, 1, 5, 8, 22, 13] 2).symm]
  calc
    wordValue (a k) [0, 1, 5, 8, 22, 13, 2] = wordValue (a k) [0, 1, 5, 8, 22, 14, 18] := context_commute k 1 [0, 1, 5, 8, 22] []
    wordValue (a k) [0, 1, 5, 8, 22, 14, 18] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18] := (context_commute k 4 [0, 1, 5, 8] [18]).symm
lemma extend_4_2 : a k 2*normalRep k ⟨(2,1),by decide⟩=normalRep k ⟨(7,1),by decide⟩ := by
  change a k 2*wordValue (a k) [1, 5, 8, 22, 13] = wordValue (a k) [1, 5, 8, 21, 9, 18]
  rw [show a k 2*wordValue (a k) [1, 5, 8, 22, 13]=wordValue (a k) [1, 5, 8, 22, 13, 2] from (word_snoc (a k) [1, 5, 8, 22, 13] 2).symm]
  calc
    wordValue (a k) [1, 5, 8, 22, 13, 2] = wordValue (a k) [1, 5, 8, 22, 14, 18] := context_commute k 1 [1, 5, 8, 22] []
    wordValue (a k) [1, 5, 8, 22, 14, 18] = wordValue (a k) [1, 5, 8, 21, 9, 18] := (context_commute k 4 [1, 5, 8] [18]).symm
lemma extend_5_2 : a k 2*normalRep k ⟨(2,2),by decide⟩=normalRep k ⟨(7,2),by decide⟩ := by
  change a k 2*e k 2=a k 2*1
  rw [av]
  norm_num [arrowSource]

lemma extend_6_2 : a k 2*normalRep k ⟨(2,6),by decide⟩=normalRep k ⟨(7,6),by decide⟩ := by
  change a k 2*wordValue (a k) [5, 8, 22, 13] = wordValue (a k) [5, 8, 21, 9, 18]
  rw [show a k 2*wordValue (a k) [5, 8, 22, 13]=wordValue (a k) [5, 8, 22, 13, 2] from (word_snoc (a k) [5, 8, 22, 13] 2).symm]
  calc
    wordValue (a k) [5, 8, 22, 13, 2] = wordValue (a k) [5, 8, 22, 14, 18] := context_commute k 1 [5, 8, 22] []
    wordValue (a k) [5, 8, 22, 14, 18] = wordValue (a k) [5, 8, 21, 9, 18] := (context_commute k 4 [5, 8] [18]).symm
lemma extend_7_2 : a k 2*normalRep k ⟨(2,9),by decide⟩=normalRep k ⟨(7,9),by decide⟩ := by
  change a k 2*wordValue (a k) [8, 22, 13] = wordValue (a k) [8, 21, 9, 18]
  rw [show a k 2*wordValue (a k) [8, 22, 13]=wordValue (a k) [8, 22, 13, 2] from (word_snoc (a k) [8, 22, 13] 2).symm]
  calc
    wordValue (a k) [8, 22, 13, 2] = wordValue (a k) [8, 22, 14, 18] := context_commute k 1 [8, 22] []
    wordValue (a k) [8, 22, 14, 18] = wordValue (a k) [8, 21, 9, 18] := (context_commute k 4 [8] [18]).symm
lemma extend_8_2 : a k 2*normalRep k ⟨(2,13),by decide⟩=normalRep k ⟨(7,13),by decide⟩ := by
  change a k 2*wordValue (a k) [13] = wordValue (a k) [13, 2]
  rw [show a k 2*wordValue (a k) [13]=wordValue (a k) [13, 2] from (word_snoc (a k) [13] 2).symm]
  all_goals rfl
lemma extend_9_2 : a k 2*normalRep k ⟨(2,17),by decide⟩=normalRep k ⟨(7,17),by decide⟩ := by
  change a k 2*wordValue (a k) [22, 13] = wordValue (a k) [21, 9, 18]
  rw [show a k 2*wordValue (a k) [22, 13]=wordValue (a k) [22, 13, 2] from (word_snoc (a k) [22, 13] 2).symm]
  calc
    wordValue (a k) [22, 13, 2] = wordValue (a k) [22, 14, 18] := context_commute k 1 [22] []
    wordValue (a k) [22, 14, 18] = wordValue (a k) [21, 9, 18] := (context_commute k 4 [] [18]).symm
lemma extend_10_3 : a k 3*normalRep k ⟨(3,0),by decide⟩=normalRep k ⟨(18,0),by decide⟩ := by
  change a k 3*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3]
  rw [show a k 3*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10]=wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3] from (word_snoc (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10] 3).symm]
  all_goals rfl
lemma extend_11_3 : a k 3*normalRep k ⟨(3,1),by decide⟩=normalRep k ⟨(18,1),by decide⟩ := by
  change a k 3*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10] = wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3]
  rw [show a k 3*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10]=wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3] from (word_snoc (a k) [1, 5, 8, 21, 9, 18, 6, 10] 3).symm]
  all_goals rfl
lemma extend_12_3 : a k 3*normalRep k ⟨(3,2),by decide⟩=normalRep k ⟨(18,2),by decide⟩ := by
  change a k 3*wordValue (a k) [2, 6, 10] = wordValue (a k) [2, 6, 10, 3]
  rw [show a k 3*wordValue (a k) [2, 6, 10]=wordValue (a k) [2, 6, 10, 3] from (word_snoc (a k) [2, 6, 10] 3).symm]
  all_goals rfl
lemma extend_13_3 : a k 3*normalRep k ⟨(3,3),by decide⟩=normalRep k ⟨(18,3),by decide⟩ := by
  change a k 3*e k 3=a k 3*1
  rw [av]
  norm_num [arrowSource]

lemma extend_14_3 : a k 3*normalRep k ⟨(3,6),by decide⟩=normalRep k ⟨(18,6),by decide⟩ := by
  change a k 3*wordValue (a k) [5, 8, 21, 9, 18, 6, 10] = wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3]
  rw [show a k 3*wordValue (a k) [5, 8, 21, 9, 18, 6, 10]=wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3] from (word_snoc (a k) [5, 8, 21, 9, 18, 6, 10] 3).symm]
  all_goals rfl
lemma extend_15_3 : a k 3*normalRep k ⟨(3,7),by decide⟩=normalRep k ⟨(18,7),by decide⟩ := by
  change a k 3*wordValue (a k) [6, 10] = wordValue (a k) [6, 10, 3]
  rw [show a k 3*wordValue (a k) [6, 10]=wordValue (a k) [6, 10, 3] from (word_snoc (a k) [6, 10] 3).symm]
  all_goals rfl
lemma extend_16_3 : a k 3*normalRep k ⟨(3,9),by decide⟩=normalRep k ⟨(18,9),by decide⟩ := by
  change a k 3*wordValue (a k) [8, 21, 9, 18, 6, 10] = wordValue (a k) [8, 21, 9, 18, 6, 10, 3]
  rw [show a k 3*wordValue (a k) [8, 21, 9, 18, 6, 10]=wordValue (a k) [8, 21, 9, 18, 6, 10, 3] from (word_snoc (a k) [8, 21, 9, 18, 6, 10] 3).symm]
  all_goals rfl
lemma extend_17_3 : a k 3*normalRep k ⟨(3,10),by decide⟩=normalRep k ⟨(18,10),by decide⟩ := by
  change a k 3*wordValue (a k) [9, 18, 6, 10] = wordValue (a k) [9, 18, 6, 10, 3]
  rw [show a k 3*wordValue (a k) [9, 18, 6, 10]=wordValue (a k) [9, 18, 6, 10, 3] from (word_snoc (a k) [9, 18, 6, 10] 3).symm]
  all_goals rfl
lemma extend_18_3 : a k 3*normalRep k ⟨(3,11),by decide⟩=normalRep k ⟨(18,11),by decide⟩ := by
  change a k 3*wordValue (a k) [10] = wordValue (a k) [10, 3]
  rw [show a k 3*wordValue (a k) [10]=wordValue (a k) [10, 3] from (word_snoc (a k) [10] 3).symm]
  all_goals rfl
lemma extend_19_3 : a k 3*normalRep k ⟨(3,13),by decide⟩=normalRep k ⟨(18,13),by decide⟩ := by
  change a k 3*wordValue (a k) [13, 2, 6, 10] = wordValue (a k) [13, 2, 6, 10, 3]
  rw [show a k 3*wordValue (a k) [13, 2, 6, 10]=wordValue (a k) [13, 2, 6, 10, 3] from (word_snoc (a k) [13, 2, 6, 10] 3).symm]
  all_goals rfl
lemma extend_20_3 : a k 3*normalRep k ⟨(3,14),by decide⟩=normalRep k ⟨(18,14),by decide⟩ := by
  change a k 3*wordValue (a k) [15, 10] = wordValue (a k) [15, 10, 3]
  rw [show a k 3*wordValue (a k) [15, 10]=wordValue (a k) [15, 10, 3] from (word_snoc (a k) [15, 10] 3).symm]
  all_goals rfl
lemma extend_21_3 : a k 3*normalRep k ⟨(3,16),by decide⟩=normalRep k ⟨(18,16),by decide⟩ := by
  change a k 3*wordValue (a k) [18, 6, 10] = wordValue (a k) [18, 6, 10, 3]
  rw [show a k 3*wordValue (a k) [18, 6, 10]=wordValue (a k) [18, 6, 10, 3] from (word_snoc (a k) [18, 6, 10] 3).symm]
  all_goals rfl
lemma extend_22_3 : a k 3*normalRep k ⟨(3,17),by decide⟩=normalRep k ⟨(18,17),by decide⟩ := by
  change a k 3*wordValue (a k) [21, 9, 18, 6, 10] = wordValue (a k) [21, 9, 18, 6, 10, 3]
  rw [show a k 3*wordValue (a k) [21, 9, 18, 6, 10]=wordValue (a k) [21, 9, 18, 6, 10, 3] from (word_snoc (a k) [21, 9, 18, 6, 10] 3).symm]
  all_goals rfl
lemma extend_23_4 : a k 4*normalRep k ⟨(4,0),by decide⟩=normalRep k ⟨(5,0),by decide⟩ := by
  change a k 4*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7]=wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7, 4] from (word_snoc (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7] 4).symm]
  all_goals rfl
lemma extend_24_4 : a k 4*normalRep k ⟨(4,1),by decide⟩=normalRep k ⟨(5,1),by decide⟩ := by
  change a k 4*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7] = wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7]=wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7, 4] from (word_snoc (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7] 4).symm]
  all_goals rfl
lemma extend_25_4 : a k 4*normalRep k ⟨(4,2),by decide⟩=normalRep k ⟨(5,2),by decide⟩ := by
  change a k 4*wordValue (a k) [2, 6, 10, 3, 20, 7] = wordValue (a k) [2, 6, 10, 3, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [2, 6, 10, 3, 20, 7]=wordValue (a k) [2, 6, 10, 3, 20, 7, 4] from (word_snoc (a k) [2, 6, 10, 3, 20, 7] 4).symm]
  all_goals rfl
lemma extend_26_4 : a k 4*normalRep k ⟨(4,3),by decide⟩=normalRep k ⟨(5,3),by decide⟩ := by
  change a k 4*wordValue (a k) [3, 20, 7] = wordValue (a k) [3, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [3, 20, 7]=wordValue (a k) [3, 20, 7, 4] from (word_snoc (a k) [3, 20, 7] 4).symm]
  all_goals rfl
lemma extend_27_4 : a k 4*normalRep k ⟨(4,4),by decide⟩=normalRep k ⟨(5,4),by decide⟩ := by
  change a k 4*e k 4=a k 4*1
  rw [av]
  norm_num [arrowSource]

lemma extend_28_4 : a k 4*normalRep k ⟨(4,6),by decide⟩=normalRep k ⟨(5,6),by decide⟩ := by
  change a k 4*wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 20, 7] = wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 20, 7]=wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 20, 7, 4] from (word_snoc (a k) [5, 8, 21, 9, 18, 6, 10, 3, 20, 7] 4).symm]
  all_goals rfl
lemma extend_29_4 : a k 4*normalRep k ⟨(4,7),by decide⟩=normalRep k ⟨(5,7),by decide⟩ := by
  change a k 4*wordValue (a k) [6, 10, 3, 20, 7] = wordValue (a k) [6, 10, 3, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [6, 10, 3, 20, 7]=wordValue (a k) [6, 10, 3, 20, 7, 4] from (word_snoc (a k) [6, 10, 3, 20, 7] 4).symm]
  all_goals rfl
lemma extend_30_4 : a k 4*normalRep k ⟨(4,8),by decide⟩=normalRep k ⟨(5,8),by decide⟩ := by
  change a k 4*wordValue (a k) [7] = wordValue (a k) [7, 4]
  rw [show a k 4*wordValue (a k) [7]=wordValue (a k) [7, 4] from (word_snoc (a k) [7] 4).symm]
  all_goals rfl
lemma extend_31_4 : a k 4*normalRep k ⟨(4,9),by decide⟩=normalRep k ⟨(5,9),by decide⟩ := by
  change a k 4*wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 20, 7] = wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 20, 7]=wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 20, 7, 4] from (word_snoc (a k) [8, 21, 9, 18, 6, 10, 3, 20, 7] 4).symm]
  all_goals rfl
lemma extend_32_4 : a k 4*normalRep k ⟨(4,10),by decide⟩=normalRep k ⟨(5,10),by decide⟩ := by
  change a k 4*wordValue (a k) [9, 18, 6, 10, 3, 20, 7] = wordValue (a k) [9, 18, 6, 10, 3, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [9, 18, 6, 10, 3, 20, 7]=wordValue (a k) [9, 18, 6, 10, 3, 20, 7, 4] from (word_snoc (a k) [9, 18, 6, 10, 3, 20, 7] 4).symm]
  all_goals rfl
lemma extend_33_4 : a k 4*normalRep k ⟨(4,11),by decide⟩=normalRep k ⟨(5,11),by decide⟩ := by
  change a k 4*wordValue (a k) [10, 3, 20, 7] = wordValue (a k) [10, 3, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [10, 3, 20, 7]=wordValue (a k) [10, 3, 20, 7, 4] from (word_snoc (a k) [10, 3, 20, 7] 4).symm]
  all_goals rfl
lemma extend_34_4 : a k 4*normalRep k ⟨(4,12),by decide⟩=normalRep k ⟨(5,12),by decide⟩ := by
  change a k 4*wordValue (a k) [12, 20, 7] = wordValue (a k) [12, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [12, 20, 7]=wordValue (a k) [12, 20, 7, 4] from (word_snoc (a k) [12, 20, 7] 4).symm]
  all_goals rfl
lemma extend_35_4 : a k 4*normalRep k ⟨(4,13),by decide⟩=normalRep k ⟨(5,13),by decide⟩ := by
  change a k 4*wordValue (a k) [13, 2, 6, 10, 3, 20, 7] = wordValue (a k) [13, 2, 6, 10, 3, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [13, 2, 6, 10, 3, 20, 7]=wordValue (a k) [13, 2, 6, 10, 3, 20, 7, 4] from (word_snoc (a k) [13, 2, 6, 10, 3, 20, 7] 4).symm]
  all_goals rfl
lemma extend_36_4 : a k 4*normalRep k ⟨(4,14),by decide⟩=normalRep k ⟨(5,14),by decide⟩ := by
  change a k 4*wordValue (a k) [15, 10, 3, 20, 7] = wordValue (a k) [15, 10, 3, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [15, 10, 3, 20, 7]=wordValue (a k) [15, 10, 3, 20, 7, 4] from (word_snoc (a k) [15, 10, 3, 20, 7] 4).symm]
  all_goals rfl
lemma extend_37_4 : a k 4*normalRep k ⟨(4,15),by decide⟩=normalRep k ⟨(5,15),by decide⟩ := by
  change a k 4*wordValue (a k) [17, 12, 20, 7] = wordValue (a k) [17, 12, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [17, 12, 20, 7]=wordValue (a k) [17, 12, 20, 7, 4] from (word_snoc (a k) [17, 12, 20, 7] 4).symm]
  all_goals rfl
lemma extend_38_4 : a k 4*normalRep k ⟨(4,16),by decide⟩=normalRep k ⟨(5,16),by decide⟩ := by
  change a k 4*wordValue (a k) [18, 6, 10, 3, 20, 7] = wordValue (a k) [18, 6, 10, 3, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [18, 6, 10, 3, 20, 7]=wordValue (a k) [18, 6, 10, 3, 20, 7, 4] from (word_snoc (a k) [18, 6, 10, 3, 20, 7] 4).symm]
  all_goals rfl
lemma extend_39_4 : a k 4*normalRep k ⟨(4,17),by decide⟩=normalRep k ⟨(5,17),by decide⟩ := by
  change a k 4*wordValue (a k) [21, 9, 18, 6, 10, 3, 20, 7] = wordValue (a k) [21, 9, 18, 6, 10, 3, 20, 7, 4]
  rw [show a k 4*wordValue (a k) [21, 9, 18, 6, 10, 3, 20, 7]=wordValue (a k) [21, 9, 18, 6, 10, 3, 20, 7, 4] from (word_snoc (a k) [21, 9, 18, 6, 10, 3, 20, 7] 4).symm]
  all_goals rfl
lemma extend_40_4 : a k 4*normalRep k ⟨(4,18),by decide⟩=normalRep k ⟨(5,18),by decide⟩ := by
  change a k 4*wordValue (a k) [20, 7] = wordValue (a k) [20, 7, 4]
  rw [show a k 4*wordValue (a k) [20, 7]=wordValue (a k) [20, 7, 4] from (word_snoc (a k) [20, 7] 4).symm]
  all_goals rfl
lemma extend_60_5 : a k 5*normalRep k ⟨(6,0),by decide⟩=normalRep k ⟨(9,0),by decide⟩ := by
  change a k 5*wordValue (a k) [0, 1] = wordValue (a k) [0, 1, 5]
  rw [show a k 5*wordValue (a k) [0, 1]=wordValue (a k) [0, 1, 5] from (word_snoc (a k) [0, 1] 5).symm]
  all_goals rfl
lemma extend_61_5 : a k 5*normalRep k ⟨(6,1),by decide⟩=normalRep k ⟨(9,1),by decide⟩ := by
  change a k 5*wordValue (a k) [1] = wordValue (a k) [1, 5]
  rw [show a k 5*wordValue (a k) [1]=wordValue (a k) [1, 5] from (word_snoc (a k) [1] 5).symm]
  all_goals rfl
lemma extend_62_5 : a k 5*normalRep k ⟨(6,6),by decide⟩=normalRep k ⟨(9,6),by decide⟩ := by
  change a k 5*e k 6=a k 5*1
  rw [av]
  norm_num [arrowSource]

lemma extend_63_6 : a k 6*normalRep k ⟨(7,0),by decide⟩=normalRep k ⟨(11,0),by decide⟩ := by
  change a k 6*wordValue (a k) [0, 1, 5, 8, 21, 9, 18] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6]
  rw [show a k 6*wordValue (a k) [0, 1, 5, 8, 21, 9, 18]=wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6] from (word_snoc (a k) [0, 1, 5, 8, 21, 9, 18] 6).symm]
  all_goals rfl
lemma extend_64_6 : a k 6*normalRep k ⟨(7,1),by decide⟩=normalRep k ⟨(11,1),by decide⟩ := by
  change a k 6*wordValue (a k) [1, 5, 8, 21, 9, 18] = wordValue (a k) [1, 5, 8, 21, 9, 18, 6]
  rw [show a k 6*wordValue (a k) [1, 5, 8, 21, 9, 18]=wordValue (a k) [1, 5, 8, 21, 9, 18, 6] from (word_snoc (a k) [1, 5, 8, 21, 9, 18] 6).symm]
  all_goals rfl
lemma extend_65_6 : a k 6*normalRep k ⟨(7,2),by decide⟩=normalRep k ⟨(11,2),by decide⟩ := by
  change a k 6*wordValue (a k) [2] = wordValue (a k) [2, 6]
  rw [show a k 6*wordValue (a k) [2]=wordValue (a k) [2, 6] from (word_snoc (a k) [2] 6).symm]
  all_goals rfl
lemma extend_66_6 : a k 6*normalRep k ⟨(7,6),by decide⟩=normalRep k ⟨(11,6),by decide⟩ := by
  change a k 6*wordValue (a k) [5, 8, 21, 9, 18] = wordValue (a k) [5, 8, 21, 9, 18, 6]
  rw [show a k 6*wordValue (a k) [5, 8, 21, 9, 18]=wordValue (a k) [5, 8, 21, 9, 18, 6] from (word_snoc (a k) [5, 8, 21, 9, 18] 6).symm]
  all_goals rfl
lemma extend_67_6 : a k 6*normalRep k ⟨(7,7),by decide⟩=normalRep k ⟨(11,7),by decide⟩ := by
  change a k 6*e k 7=a k 6*1
  rw [av]
  norm_num [arrowSource]

lemma extend_68_6 : a k 6*normalRep k ⟨(7,9),by decide⟩=normalRep k ⟨(11,9),by decide⟩ := by
  change a k 6*wordValue (a k) [8, 21, 9, 18] = wordValue (a k) [8, 21, 9, 18, 6]
  rw [show a k 6*wordValue (a k) [8, 21, 9, 18]=wordValue (a k) [8, 21, 9, 18, 6] from (word_snoc (a k) [8, 21, 9, 18] 6).symm]
  all_goals rfl
lemma extend_69_6 : a k 6*normalRep k ⟨(7,10),by decide⟩=normalRep k ⟨(11,10),by decide⟩ := by
  change a k 6*wordValue (a k) [9, 18] = wordValue (a k) [9, 18, 6]
  rw [show a k 6*wordValue (a k) [9, 18]=wordValue (a k) [9, 18, 6] from (word_snoc (a k) [9, 18] 6).symm]
  all_goals rfl
lemma extend_70_6 : a k 6*normalRep k ⟨(7,13),by decide⟩=normalRep k ⟨(11,13),by decide⟩ := by
  change a k 6*wordValue (a k) [13, 2] = wordValue (a k) [13, 2, 6]
  rw [show a k 6*wordValue (a k) [13, 2]=wordValue (a k) [13, 2, 6] from (word_snoc (a k) [13, 2] 6).symm]
  all_goals rfl
lemma extend_71_6 : a k 6*normalRep k ⟨(7,16),by decide⟩=normalRep k ⟨(11,16),by decide⟩ := by
  change a k 6*wordValue (a k) [18] = wordValue (a k) [18, 6]
  rw [show a k 6*wordValue (a k) [18]=wordValue (a k) [18, 6] from (word_snoc (a k) [18] 6).symm]
  all_goals rfl
lemma extend_72_6 : a k 6*normalRep k ⟨(7,17),by decide⟩=normalRep k ⟨(11,17),by decide⟩ := by
  change a k 6*wordValue (a k) [21, 9, 18] = wordValue (a k) [21, 9, 18, 6]
  rw [show a k 6*wordValue (a k) [21, 9, 18]=wordValue (a k) [21, 9, 18, 6] from (word_snoc (a k) [21, 9, 18] 6).symm]
  all_goals rfl
lemma extend_73_7 : a k 7*normalRep k ⟨(8,0),by decide⟩=normalRep k ⟨(4,0),by decide⟩ := by
  change a k 7*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7]
  rw [show a k 7*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20]=wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7] from (word_snoc (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20] 7).symm]
  all_goals rfl
lemma extend_74_7 : a k 7*normalRep k ⟨(8,1),by decide⟩=normalRep k ⟨(4,1),by decide⟩ := by
  change a k 7*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 20] = wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7]
  rw [show a k 7*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 20]=wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 20, 7] from (word_snoc (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 20] 7).symm]
  all_goals rfl
lemma extend_75_7 : a k 7*normalRep k ⟨(8,2),by decide⟩=normalRep k ⟨(4,2),by decide⟩ := by
  change a k 7*wordValue (a k) [2, 6, 10, 3, 20] = wordValue (a k) [2, 6, 10, 3, 20, 7]
  rw [show a k 7*wordValue (a k) [2, 6, 10, 3, 20]=wordValue (a k) [2, 6, 10, 3, 20, 7] from (word_snoc (a k) [2, 6, 10, 3, 20] 7).symm]
  all_goals rfl
lemma extend_76_7 : a k 7*normalRep k ⟨(8,3),by decide⟩=normalRep k ⟨(4,3),by decide⟩ := by
  change a k 7*wordValue (a k) [3, 20] = wordValue (a k) [3, 20, 7]
  rw [show a k 7*wordValue (a k) [3, 20]=wordValue (a k) [3, 20, 7] from (word_snoc (a k) [3, 20] 7).symm]
  all_goals rfl
lemma extend_77_7 : a k 7*normalRep k ⟨(8,6),by decide⟩=normalRep k ⟨(4,6),by decide⟩ := by
  change a k 7*wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 20] = wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 20, 7]
  rw [show a k 7*wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 20]=wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 20, 7] from (word_snoc (a k) [5, 8, 21, 9, 18, 6, 10, 3, 20] 7).symm]
  all_goals rfl
lemma extend_78_7 : a k 7*normalRep k ⟨(8,7),by decide⟩=normalRep k ⟨(4,7),by decide⟩ := by
  change a k 7*wordValue (a k) [6, 10, 3, 20] = wordValue (a k) [6, 10, 3, 20, 7]
  rw [show a k 7*wordValue (a k) [6, 10, 3, 20]=wordValue (a k) [6, 10, 3, 20, 7] from (word_snoc (a k) [6, 10, 3, 20] 7).symm]
  all_goals rfl
lemma extend_79_7 : a k 7*normalRep k ⟨(8,8),by decide⟩=normalRep k ⟨(4,8),by decide⟩ := by
  change a k 7*e k 8=a k 7*1
  rw [av]
  norm_num [arrowSource]

lemma extend_80_7 : a k 7*normalRep k ⟨(8,9),by decide⟩=normalRep k ⟨(4,9),by decide⟩ := by
  change a k 7*wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 20] = wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 20, 7]
  rw [show a k 7*wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 20]=wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 20, 7] from (word_snoc (a k) [8, 21, 9, 18, 6, 10, 3, 20] 7).symm]
  all_goals rfl
lemma extend_81_7 : a k 7*normalRep k ⟨(8,10),by decide⟩=normalRep k ⟨(4,10),by decide⟩ := by
  change a k 7*wordValue (a k) [9, 18, 6, 10, 3, 20] = wordValue (a k) [9, 18, 6, 10, 3, 20, 7]
  rw [show a k 7*wordValue (a k) [9, 18, 6, 10, 3, 20]=wordValue (a k) [9, 18, 6, 10, 3, 20, 7] from (word_snoc (a k) [9, 18, 6, 10, 3, 20] 7).symm]
  all_goals rfl
lemma extend_82_7 : a k 7*normalRep k ⟨(8,11),by decide⟩=normalRep k ⟨(4,11),by decide⟩ := by
  change a k 7*wordValue (a k) [10, 3, 20] = wordValue (a k) [10, 3, 20, 7]
  rw [show a k 7*wordValue (a k) [10, 3, 20]=wordValue (a k) [10, 3, 20, 7] from (word_snoc (a k) [10, 3, 20] 7).symm]
  all_goals rfl
lemma extend_83_7 : a k 7*normalRep k ⟨(8,12),by decide⟩=normalRep k ⟨(4,12),by decide⟩ := by
  change a k 7*wordValue (a k) [12, 20] = wordValue (a k) [12, 20, 7]
  rw [show a k 7*wordValue (a k) [12, 20]=wordValue (a k) [12, 20, 7] from (word_snoc (a k) [12, 20] 7).symm]
  all_goals rfl
lemma extend_84_7 : a k 7*normalRep k ⟨(8,13),by decide⟩=normalRep k ⟨(4,13),by decide⟩ := by
  change a k 7*wordValue (a k) [13, 2, 6, 10, 3, 20] = wordValue (a k) [13, 2, 6, 10, 3, 20, 7]
  rw [show a k 7*wordValue (a k) [13, 2, 6, 10, 3, 20]=wordValue (a k) [13, 2, 6, 10, 3, 20, 7] from (word_snoc (a k) [13, 2, 6, 10, 3, 20] 7).symm]
  all_goals rfl
lemma extend_85_7 : a k 7*normalRep k ⟨(8,14),by decide⟩=normalRep k ⟨(4,14),by decide⟩ := by
  change a k 7*wordValue (a k) [15, 10, 3, 20] = wordValue (a k) [15, 10, 3, 20, 7]
  rw [show a k 7*wordValue (a k) [15, 10, 3, 20]=wordValue (a k) [15, 10, 3, 20, 7] from (word_snoc (a k) [15, 10, 3, 20] 7).symm]
  all_goals rfl
lemma extend_86_7 : a k 7*normalRep k ⟨(8,15),by decide⟩=normalRep k ⟨(4,15),by decide⟩ := by
  change a k 7*wordValue (a k) [17, 12, 20] = wordValue (a k) [17, 12, 20, 7]
  rw [show a k 7*wordValue (a k) [17, 12, 20]=wordValue (a k) [17, 12, 20, 7] from (word_snoc (a k) [17, 12, 20] 7).symm]
  all_goals rfl
lemma extend_87_7 : a k 7*normalRep k ⟨(8,16),by decide⟩=normalRep k ⟨(4,16),by decide⟩ := by
  change a k 7*wordValue (a k) [18, 6, 10, 3, 20] = wordValue (a k) [18, 6, 10, 3, 20, 7]
  rw [show a k 7*wordValue (a k) [18, 6, 10, 3, 20]=wordValue (a k) [18, 6, 10, 3, 20, 7] from (word_snoc (a k) [18, 6, 10, 3, 20] 7).symm]
  all_goals rfl
lemma extend_88_7 : a k 7*normalRep k ⟨(8,17),by decide⟩=normalRep k ⟨(4,17),by decide⟩ := by
  change a k 7*wordValue (a k) [21, 9, 18, 6, 10, 3, 20] = wordValue (a k) [21, 9, 18, 6, 10, 3, 20, 7]
  rw [show a k 7*wordValue (a k) [21, 9, 18, 6, 10, 3, 20]=wordValue (a k) [21, 9, 18, 6, 10, 3, 20, 7] from (word_snoc (a k) [21, 9, 18, 6, 10, 3, 20] 7).symm]
  all_goals rfl
lemma extend_89_7 : a k 7*normalRep k ⟨(8,18),by decide⟩=normalRep k ⟨(4,18),by decide⟩ := by
  change a k 7*wordValue (a k) [20] = wordValue (a k) [20, 7]
  rw [show a k 7*wordValue (a k) [20]=wordValue (a k) [20, 7] from (word_snoc (a k) [20] 7).symm]
  all_goals rfl
lemma extend_90_8 : a k 8*normalRep k ⟨(9,0),by decide⟩=normalRep k ⟨(17,0),by decide⟩ := by
  change a k 8*wordValue (a k) [0, 1, 5] = wordValue (a k) [0, 1, 5, 8]
  rw [show a k 8*wordValue (a k) [0, 1, 5]=wordValue (a k) [0, 1, 5, 8] from (word_snoc (a k) [0, 1, 5] 8).symm]
  all_goals rfl
lemma extend_91_8 : a k 8*normalRep k ⟨(9,1),by decide⟩=normalRep k ⟨(17,1),by decide⟩ := by
  change a k 8*wordValue (a k) [1, 5] = wordValue (a k) [1, 5, 8]
  rw [show a k 8*wordValue (a k) [1, 5]=wordValue (a k) [1, 5, 8] from (word_snoc (a k) [1, 5] 8).symm]
  all_goals rfl
lemma extend_92_8 : a k 8*normalRep k ⟨(9,6),by decide⟩=normalRep k ⟨(17,6),by decide⟩ := by
  change a k 8*wordValue (a k) [5] = wordValue (a k) [5, 8]
  rw [show a k 8*wordValue (a k) [5]=wordValue (a k) [5, 8] from (word_snoc (a k) [5] 8).symm]
  all_goals rfl
lemma extend_93_8 : a k 8*normalRep k ⟨(9,9),by decide⟩=normalRep k ⟨(17,9),by decide⟩ := by
  change a k 8*e k 9=a k 8*1
  rw [av]
  norm_num [arrowSource]

lemma extend_94_9 : a k 9*normalRep k ⟨(10,0),by decide⟩=normalRep k ⟨(16,0),by decide⟩ := by
  change a k 9*wordValue (a k) [0, 1, 5, 8, 21] = wordValue (a k) [0, 1, 5, 8, 21, 9]
  rw [show a k 9*wordValue (a k) [0, 1, 5, 8, 21]=wordValue (a k) [0, 1, 5, 8, 21, 9] from (word_snoc (a k) [0, 1, 5, 8, 21] 9).symm]
  all_goals rfl
lemma extend_95_9 : a k 9*normalRep k ⟨(10,1),by decide⟩=normalRep k ⟨(16,1),by decide⟩ := by
  change a k 9*wordValue (a k) [1, 5, 8, 21] = wordValue (a k) [1, 5, 8, 21, 9]
  rw [show a k 9*wordValue (a k) [1, 5, 8, 21]=wordValue (a k) [1, 5, 8, 21, 9] from (word_snoc (a k) [1, 5, 8, 21] 9).symm]
  all_goals rfl
lemma extend_96_9 : a k 9*normalRep k ⟨(10,6),by decide⟩=normalRep k ⟨(16,6),by decide⟩ := by
  change a k 9*wordValue (a k) [5, 8, 21] = wordValue (a k) [5, 8, 21, 9]
  rw [show a k 9*wordValue (a k) [5, 8, 21]=wordValue (a k) [5, 8, 21, 9] from (word_snoc (a k) [5, 8, 21] 9).symm]
  all_goals rfl
lemma extend_97_9 : a k 9*normalRep k ⟨(10,9),by decide⟩=normalRep k ⟨(16,9),by decide⟩ := by
  change a k 9*wordValue (a k) [8, 21] = wordValue (a k) [8, 21, 9]
  rw [show a k 9*wordValue (a k) [8, 21]=wordValue (a k) [8, 21, 9] from (word_snoc (a k) [8, 21] 9).symm]
  all_goals rfl
lemma extend_98_9 : a k 9*normalRep k ⟨(10,10),by decide⟩=normalRep k ⟨(16,10),by decide⟩ := by
  change a k 9*e k 10=a k 9*1
  rw [av]
  norm_num [arrowSource]

lemma extend_99_9 : a k 9*normalRep k ⟨(10,17),by decide⟩=normalRep k ⟨(16,17),by decide⟩ := by
  change a k 9*wordValue (a k) [21] = wordValue (a k) [21, 9]
  rw [show a k 9*wordValue (a k) [21]=wordValue (a k) [21, 9] from (word_snoc (a k) [21] 9).symm]
  all_goals rfl
lemma extend_100_10 : a k 10*normalRep k ⟨(11,0),by decide⟩=normalRep k ⟨(3,0),by decide⟩ := by
  change a k 10*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10]
  rw [show a k 10*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6]=wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10] from (word_snoc (a k) [0, 1, 5, 8, 21, 9, 18, 6] 10).symm]
  all_goals rfl
lemma extend_100_11 : a k 11*normalRep k ⟨(11,0),by decide⟩=normalRep k ⟨(12,0),by decide⟩ := by
  change a k 11*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 11]
  rw [show a k 11*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6]=wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 11] from (word_snoc (a k) [0, 1, 5, 8, 21, 9, 18, 6] 11).symm]
  all_goals rfl
lemma extend_101_10 : a k 10*normalRep k ⟨(11,1),by decide⟩=normalRep k ⟨(3,1),by decide⟩ := by
  change a k 10*wordValue (a k) [1, 5, 8, 21, 9, 18, 6] = wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10]
  rw [show a k 10*wordValue (a k) [1, 5, 8, 21, 9, 18, 6]=wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10] from (word_snoc (a k) [1, 5, 8, 21, 9, 18, 6] 10).symm]
  all_goals rfl
lemma extend_101_11 : a k 11*normalRep k ⟨(11,1),by decide⟩=normalRep k ⟨(12,1),by decide⟩ := by
  change a k 11*wordValue (a k) [1, 5, 8, 21, 9, 18, 6] = wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 11]
  rw [show a k 11*wordValue (a k) [1, 5, 8, 21, 9, 18, 6]=wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 11] from (word_snoc (a k) [1, 5, 8, 21, 9, 18, 6] 11).symm]
  all_goals rfl
lemma extend_102_10 : a k 10*normalRep k ⟨(11,2),by decide⟩=normalRep k ⟨(3,2),by decide⟩ := by
  change a k 10*wordValue (a k) [2, 6] = wordValue (a k) [2, 6, 10]
  rw [show a k 10*wordValue (a k) [2, 6]=wordValue (a k) [2, 6, 10] from (word_snoc (a k) [2, 6] 10).symm]
  all_goals rfl
lemma extend_102_11 : a k 11*normalRep k ⟨(11,2),by decide⟩=normalRep k ⟨(12,2),by decide⟩ := by
  change a k 11*wordValue (a k) [2, 6] = wordValue (a k) [2, 6, 11]
  rw [show a k 11*wordValue (a k) [2, 6]=wordValue (a k) [2, 6, 11] from (word_snoc (a k) [2, 6] 11).symm]
  all_goals rfl
lemma extend_103_10 : a k 10*normalRep k ⟨(11,6),by decide⟩=normalRep k ⟨(3,6),by decide⟩ := by
  change a k 10*wordValue (a k) [5, 8, 21, 9, 18, 6] = wordValue (a k) [5, 8, 21, 9, 18, 6, 10]
  rw [show a k 10*wordValue (a k) [5, 8, 21, 9, 18, 6]=wordValue (a k) [5, 8, 21, 9, 18, 6, 10] from (word_snoc (a k) [5, 8, 21, 9, 18, 6] 10).symm]
  all_goals rfl
lemma extend_103_11 : a k 11*normalRep k ⟨(11,6),by decide⟩=normalRep k ⟨(12,6),by decide⟩ := by
  change a k 11*wordValue (a k) [5, 8, 21, 9, 18, 6] = wordValue (a k) [5, 8, 21, 9, 18, 6, 11]
  rw [show a k 11*wordValue (a k) [5, 8, 21, 9, 18, 6]=wordValue (a k) [5, 8, 21, 9, 18, 6, 11] from (word_snoc (a k) [5, 8, 21, 9, 18, 6] 11).symm]
  all_goals rfl
lemma extend_104_10 : a k 10*normalRep k ⟨(11,7),by decide⟩=normalRep k ⟨(3,7),by decide⟩ := by
  change a k 10*wordValue (a k) [6] = wordValue (a k) [6, 10]
  rw [show a k 10*wordValue (a k) [6]=wordValue (a k) [6, 10] from (word_snoc (a k) [6] 10).symm]
  all_goals rfl
lemma extend_104_11 : a k 11*normalRep k ⟨(11,7),by decide⟩=normalRep k ⟨(12,7),by decide⟩ := by
  change a k 11*wordValue (a k) [6] = wordValue (a k) [6, 11]
  rw [show a k 11*wordValue (a k) [6]=wordValue (a k) [6, 11] from (word_snoc (a k) [6] 11).symm]
  all_goals rfl
lemma extend_105_10 : a k 10*normalRep k ⟨(11,9),by decide⟩=normalRep k ⟨(3,9),by decide⟩ := by
  change a k 10*wordValue (a k) [8, 21, 9, 18, 6] = wordValue (a k) [8, 21, 9, 18, 6, 10]
  rw [show a k 10*wordValue (a k) [8, 21, 9, 18, 6]=wordValue (a k) [8, 21, 9, 18, 6, 10] from (word_snoc (a k) [8, 21, 9, 18, 6] 10).symm]
  all_goals rfl
lemma extend_105_11 : a k 11*normalRep k ⟨(11,9),by decide⟩=normalRep k ⟨(12,9),by decide⟩ := by
  change a k 11*wordValue (a k) [8, 21, 9, 18, 6] = wordValue (a k) [8, 21, 9, 18, 6, 11]
  rw [show a k 11*wordValue (a k) [8, 21, 9, 18, 6]=wordValue (a k) [8, 21, 9, 18, 6, 11] from (word_snoc (a k) [8, 21, 9, 18, 6] 11).symm]
  all_goals rfl
lemma extend_106_10 : a k 10*normalRep k ⟨(11,10),by decide⟩=normalRep k ⟨(3,10),by decide⟩ := by
  change a k 10*wordValue (a k) [9, 18, 6] = wordValue (a k) [9, 18, 6, 10]
  rw [show a k 10*wordValue (a k) [9, 18, 6]=wordValue (a k) [9, 18, 6, 10] from (word_snoc (a k) [9, 18, 6] 10).symm]
  all_goals rfl
lemma extend_106_11 : a k 11*normalRep k ⟨(11,10),by decide⟩=normalRep k ⟨(12,10),by decide⟩ := by
  change a k 11*wordValue (a k) [9, 18, 6] = wordValue (a k) [9, 18, 6, 11]
  rw [show a k 11*wordValue (a k) [9, 18, 6]=wordValue (a k) [9, 18, 6, 11] from (word_snoc (a k) [9, 18, 6] 11).symm]
  all_goals rfl
lemma extend_107_10 : a k 10*normalRep k ⟨(11,11),by decide⟩=normalRep k ⟨(3,11),by decide⟩ := by
  change a k 10*e k 11=a k 10*1
  rw [av]
  norm_num [arrowSource]

lemma extend_107_11 : a k 11*normalRep k ⟨(11,11),by decide⟩=normalRep k ⟨(12,11),by decide⟩ := by
  change a k 11*e k 11=a k 11*1
  rw [av]
  norm_num [arrowSource]

lemma extend_108_10 : a k 10*normalRep k ⟨(11,13),by decide⟩=normalRep k ⟨(3,13),by decide⟩ := by
  change a k 10*wordValue (a k) [13, 2, 6] = wordValue (a k) [13, 2, 6, 10]
  rw [show a k 10*wordValue (a k) [13, 2, 6]=wordValue (a k) [13, 2, 6, 10] from (word_snoc (a k) [13, 2, 6] 10).symm]
  all_goals rfl
lemma extend_108_11 : a k 11*normalRep k ⟨(11,13),by decide⟩=normalRep k ⟨(12,13),by decide⟩ := by
  change a k 11*wordValue (a k) [13, 2, 6] = wordValue (a k) [13, 2, 6, 11]
  rw [show a k 11*wordValue (a k) [13, 2, 6]=wordValue (a k) [13, 2, 6, 11] from (word_snoc (a k) [13, 2, 6] 11).symm]
  all_goals rfl
lemma extend_109_10 : a k 10*normalRep k ⟨(11,14),by decide⟩=normalRep k ⟨(3,14),by decide⟩ := by
  change a k 10*wordValue (a k) [15] = wordValue (a k) [15, 10]
  rw [show a k 10*wordValue (a k) [15]=wordValue (a k) [15, 10] from (word_snoc (a k) [15] 10).symm]
  all_goals rfl
lemma extend_109_11 : a k 11*normalRep k ⟨(11,14),by decide⟩=normalRep k ⟨(12,14),by decide⟩ := by
  change a k 11*wordValue (a k) [15] = wordValue (a k) [15, 11]
  rw [show a k 11*wordValue (a k) [15]=wordValue (a k) [15, 11] from (word_snoc (a k) [15] 11).symm]
  all_goals rfl
lemma extend_110_10 : a k 10*normalRep k ⟨(11,16),by decide⟩=normalRep k ⟨(3,16),by decide⟩ := by
  change a k 10*wordValue (a k) [18, 6] = wordValue (a k) [18, 6, 10]
  rw [show a k 10*wordValue (a k) [18, 6]=wordValue (a k) [18, 6, 10] from (word_snoc (a k) [18, 6] 10).symm]
  all_goals rfl
lemma extend_110_11 : a k 11*normalRep k ⟨(11,16),by decide⟩=normalRep k ⟨(12,16),by decide⟩ := by
  change a k 11*wordValue (a k) [18, 6] = wordValue (a k) [18, 6, 11]
  rw [show a k 11*wordValue (a k) [18, 6]=wordValue (a k) [18, 6, 11] from (word_snoc (a k) [18, 6] 11).symm]
  all_goals rfl
lemma extend_111_10 : a k 10*normalRep k ⟨(11,17),by decide⟩=normalRep k ⟨(3,17),by decide⟩ := by
  change a k 10*wordValue (a k) [21, 9, 18, 6] = wordValue (a k) [21, 9, 18, 6, 10]
  rw [show a k 10*wordValue (a k) [21, 9, 18, 6]=wordValue (a k) [21, 9, 18, 6, 10] from (word_snoc (a k) [21, 9, 18, 6] 10).symm]
  all_goals rfl
lemma extend_111_11 : a k 11*normalRep k ⟨(11,17),by decide⟩=normalRep k ⟨(12,17),by decide⟩ := by
  change a k 11*wordValue (a k) [21, 9, 18, 6] = wordValue (a k) [21, 9, 18, 6, 11]
  rw [show a k 11*wordValue (a k) [21, 9, 18, 6]=wordValue (a k) [21, 9, 18, 6, 11] from (word_snoc (a k) [21, 9, 18, 6] 11).symm]
  all_goals rfl
lemma extend_112_12 : a k 12*normalRep k ⟨(12,0),by decide⟩=normalRep k ⟨(18,0),by decide⟩ := by
  change a k 12*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 11] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3]
  rw [show a k 12*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 11]=wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 11, 12] from (word_snoc (a k) [0, 1, 5, 8, 21, 9, 18, 6, 11] 12).symm]
  calc
    wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 11, 12] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3] := (context_commute k 0 [0, 1, 5, 8, 21, 9, 18, 6] []).symm
lemma extend_113_12 : a k 12*normalRep k ⟨(12,1),by decide⟩=normalRep k ⟨(18,1),by decide⟩ := by
  change a k 12*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 11] = wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3]
  rw [show a k 12*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 11]=wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 11, 12] from (word_snoc (a k) [1, 5, 8, 21, 9, 18, 6, 11] 12).symm]
  calc
    wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 11, 12] = wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3] := (context_commute k 0 [1, 5, 8, 21, 9, 18, 6] []).symm
lemma extend_114_12 : a k 12*normalRep k ⟨(12,2),by decide⟩=normalRep k ⟨(18,2),by decide⟩ := by
  change a k 12*wordValue (a k) [2, 6, 11] = wordValue (a k) [2, 6, 10, 3]
  rw [show a k 12*wordValue (a k) [2, 6, 11]=wordValue (a k) [2, 6, 11, 12] from (word_snoc (a k) [2, 6, 11] 12).symm]
  calc
    wordValue (a k) [2, 6, 11, 12] = wordValue (a k) [2, 6, 10, 3] := (context_commute k 0 [2, 6] []).symm
lemma extend_115_12 : a k 12*normalRep k ⟨(12,6),by decide⟩=normalRep k ⟨(18,6),by decide⟩ := by
  change a k 12*wordValue (a k) [5, 8, 21, 9, 18, 6, 11] = wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3]
  rw [show a k 12*wordValue (a k) [5, 8, 21, 9, 18, 6, 11]=wordValue (a k) [5, 8, 21, 9, 18, 6, 11, 12] from (word_snoc (a k) [5, 8, 21, 9, 18, 6, 11] 12).symm]
  calc
    wordValue (a k) [5, 8, 21, 9, 18, 6, 11, 12] = wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3] := (context_commute k 0 [5, 8, 21, 9, 18, 6] []).symm
lemma extend_116_12 : a k 12*normalRep k ⟨(12,7),by decide⟩=normalRep k ⟨(18,7),by decide⟩ := by
  change a k 12*wordValue (a k) [6, 11] = wordValue (a k) [6, 10, 3]
  rw [show a k 12*wordValue (a k) [6, 11]=wordValue (a k) [6, 11, 12] from (word_snoc (a k) [6, 11] 12).symm]
  calc
    wordValue (a k) [6, 11, 12] = wordValue (a k) [6, 10, 3] := (context_commute k 0 [6] []).symm
lemma extend_117_12 : a k 12*normalRep k ⟨(12,9),by decide⟩=normalRep k ⟨(18,9),by decide⟩ := by
  change a k 12*wordValue (a k) [8, 21, 9, 18, 6, 11] = wordValue (a k) [8, 21, 9, 18, 6, 10, 3]
  rw [show a k 12*wordValue (a k) [8, 21, 9, 18, 6, 11]=wordValue (a k) [8, 21, 9, 18, 6, 11, 12] from (word_snoc (a k) [8, 21, 9, 18, 6, 11] 12).symm]
  calc
    wordValue (a k) [8, 21, 9, 18, 6, 11, 12] = wordValue (a k) [8, 21, 9, 18, 6, 10, 3] := (context_commute k 0 [8, 21, 9, 18, 6] []).symm
lemma extend_118_12 : a k 12*normalRep k ⟨(12,10),by decide⟩=normalRep k ⟨(18,10),by decide⟩ := by
  change a k 12*wordValue (a k) [9, 18, 6, 11] = wordValue (a k) [9, 18, 6, 10, 3]
  rw [show a k 12*wordValue (a k) [9, 18, 6, 11]=wordValue (a k) [9, 18, 6, 11, 12] from (word_snoc (a k) [9, 18, 6, 11] 12).symm]
  calc
    wordValue (a k) [9, 18, 6, 11, 12] = wordValue (a k) [9, 18, 6, 10, 3] := (context_commute k 0 [9, 18, 6] []).symm
lemma extend_119_12 : a k 12*normalRep k ⟨(12,11),by decide⟩=normalRep k ⟨(18,11),by decide⟩ := by
  change a k 12*wordValue (a k) [11] = wordValue (a k) [10, 3]
  rw [show a k 12*wordValue (a k) [11]=wordValue (a k) [11, 12] from (word_snoc (a k) [11] 12).symm]
  calc
    wordValue (a k) [11, 12] = wordValue (a k) [10, 3] := (context_commute k 0 [] []).symm
lemma extend_120_12 : a k 12*normalRep k ⟨(12,12),by decide⟩=normalRep k ⟨(18,12),by decide⟩ := by
  change a k 12*e k 12=a k 12*1
  rw [av]
  norm_num [arrowSource]

lemma extend_121_12 : a k 12*normalRep k ⟨(12,13),by decide⟩=normalRep k ⟨(18,13),by decide⟩ := by
  change a k 12*wordValue (a k) [13, 2, 6, 11] = wordValue (a k) [13, 2, 6, 10, 3]
  rw [show a k 12*wordValue (a k) [13, 2, 6, 11]=wordValue (a k) [13, 2, 6, 11, 12] from (word_snoc (a k) [13, 2, 6, 11] 12).symm]
  calc
    wordValue (a k) [13, 2, 6, 11, 12] = wordValue (a k) [13, 2, 6, 10, 3] := (context_commute k 0 [13, 2, 6] []).symm
lemma extend_122_12 : a k 12*normalRep k ⟨(12,14),by decide⟩=normalRep k ⟨(18,14),by decide⟩ := by
  change a k 12*wordValue (a k) [15, 11] = wordValue (a k) [15, 10, 3]
  rw [show a k 12*wordValue (a k) [15, 11]=wordValue (a k) [15, 11, 12] from (word_snoc (a k) [15, 11] 12).symm]
  calc
    wordValue (a k) [15, 11, 12] = wordValue (a k) [15, 10, 3] := (context_commute k 0 [15] []).symm
lemma extend_123_12 : a k 12*normalRep k ⟨(12,15),by decide⟩=normalRep k ⟨(18,15),by decide⟩ := by
  change a k 12*wordValue (a k) [17] = wordValue (a k) [17, 12]
  rw [show a k 12*wordValue (a k) [17]=wordValue (a k) [17, 12] from (word_snoc (a k) [17] 12).symm]
  all_goals rfl
lemma extend_124_12 : a k 12*normalRep k ⟨(12,16),by decide⟩=normalRep k ⟨(18,16),by decide⟩ := by
  change a k 12*wordValue (a k) [18, 6, 11] = wordValue (a k) [18, 6, 10, 3]
  rw [show a k 12*wordValue (a k) [18, 6, 11]=wordValue (a k) [18, 6, 11, 12] from (word_snoc (a k) [18, 6, 11] 12).symm]
  calc
    wordValue (a k) [18, 6, 11, 12] = wordValue (a k) [18, 6, 10, 3] := (context_commute k 0 [18, 6] []).symm
lemma extend_125_12 : a k 12*normalRep k ⟨(12,17),by decide⟩=normalRep k ⟨(18,17),by decide⟩ := by
  change a k 12*wordValue (a k) [21, 9, 18, 6, 11] = wordValue (a k) [21, 9, 18, 6, 10, 3]
  rw [show a k 12*wordValue (a k) [21, 9, 18, 6, 11]=wordValue (a k) [21, 9, 18, 6, 11, 12] from (word_snoc (a k) [21, 9, 18, 6, 11] 12).symm]
  calc
    wordValue (a k) [21, 9, 18, 6, 11, 12] = wordValue (a k) [21, 9, 18, 6, 10, 3] := (context_commute k 0 [21, 9, 18, 6] []).symm
lemma extend_126_13 : a k 13*normalRep k ⟨(13,0),by decide⟩=normalRep k ⟨(2,0),by decide⟩ := by
  change a k 13*wordValue (a k) [0, 1, 5, 8, 22] = wordValue (a k) [0, 1, 5, 8, 22, 13]
  rw [show a k 13*wordValue (a k) [0, 1, 5, 8, 22]=wordValue (a k) [0, 1, 5, 8, 22, 13] from (word_snoc (a k) [0, 1, 5, 8, 22] 13).symm]
  all_goals rfl
lemma extend_126_14 : a k 14*normalRep k ⟨(13,0),by decide⟩=normalRep k ⟨(16,0),by decide⟩ := by
  change a k 14*wordValue (a k) [0, 1, 5, 8, 22] = wordValue (a k) [0, 1, 5, 8, 21, 9]
  rw [show a k 14*wordValue (a k) [0, 1, 5, 8, 22]=wordValue (a k) [0, 1, 5, 8, 22, 14] from (word_snoc (a k) [0, 1, 5, 8, 22] 14).symm]
  calc
    wordValue (a k) [0, 1, 5, 8, 22, 14] = wordValue (a k) [0, 1, 5, 8, 21, 9] := (context_commute k 4 [0, 1, 5, 8] []).symm
lemma extend_127_13 : a k 13*normalRep k ⟨(13,1),by decide⟩=normalRep k ⟨(2,1),by decide⟩ := by
  change a k 13*wordValue (a k) [1, 5, 8, 22] = wordValue (a k) [1, 5, 8, 22, 13]
  rw [show a k 13*wordValue (a k) [1, 5, 8, 22]=wordValue (a k) [1, 5, 8, 22, 13] from (word_snoc (a k) [1, 5, 8, 22] 13).symm]
  all_goals rfl
lemma extend_127_14 : a k 14*normalRep k ⟨(13,1),by decide⟩=normalRep k ⟨(16,1),by decide⟩ := by
  change a k 14*wordValue (a k) [1, 5, 8, 22] = wordValue (a k) [1, 5, 8, 21, 9]
  rw [show a k 14*wordValue (a k) [1, 5, 8, 22]=wordValue (a k) [1, 5, 8, 22, 14] from (word_snoc (a k) [1, 5, 8, 22] 14).symm]
  calc
    wordValue (a k) [1, 5, 8, 22, 14] = wordValue (a k) [1, 5, 8, 21, 9] := (context_commute k 4 [1, 5, 8] []).symm
lemma extend_128_13 : a k 13*normalRep k ⟨(13,6),by decide⟩=normalRep k ⟨(2,6),by decide⟩ := by
  change a k 13*wordValue (a k) [5, 8, 22] = wordValue (a k) [5, 8, 22, 13]
  rw [show a k 13*wordValue (a k) [5, 8, 22]=wordValue (a k) [5, 8, 22, 13] from (word_snoc (a k) [5, 8, 22] 13).symm]
  all_goals rfl
lemma extend_128_14 : a k 14*normalRep k ⟨(13,6),by decide⟩=normalRep k ⟨(16,6),by decide⟩ := by
  change a k 14*wordValue (a k) [5, 8, 22] = wordValue (a k) [5, 8, 21, 9]
  rw [show a k 14*wordValue (a k) [5, 8, 22]=wordValue (a k) [5, 8, 22, 14] from (word_snoc (a k) [5, 8, 22] 14).symm]
  calc
    wordValue (a k) [5, 8, 22, 14] = wordValue (a k) [5, 8, 21, 9] := (context_commute k 4 [5, 8] []).symm
lemma extend_129_13 : a k 13*normalRep k ⟨(13,9),by decide⟩=normalRep k ⟨(2,9),by decide⟩ := by
  change a k 13*wordValue (a k) [8, 22] = wordValue (a k) [8, 22, 13]
  rw [show a k 13*wordValue (a k) [8, 22]=wordValue (a k) [8, 22, 13] from (word_snoc (a k) [8, 22] 13).symm]
  all_goals rfl
lemma extend_129_14 : a k 14*normalRep k ⟨(13,9),by decide⟩=normalRep k ⟨(16,9),by decide⟩ := by
  change a k 14*wordValue (a k) [8, 22] = wordValue (a k) [8, 21, 9]
  rw [show a k 14*wordValue (a k) [8, 22]=wordValue (a k) [8, 22, 14] from (word_snoc (a k) [8, 22] 14).symm]
  calc
    wordValue (a k) [8, 22, 14] = wordValue (a k) [8, 21, 9] := (context_commute k 4 [8] []).symm
lemma extend_130_13 : a k 13*normalRep k ⟨(13,13),by decide⟩=normalRep k ⟨(2,13),by decide⟩ := by
  change a k 13*e k 13=a k 13*1
  rw [av]
  norm_num [arrowSource]

lemma extend_130_14 : a k 14*normalRep k ⟨(13,13),by decide⟩=normalRep k ⟨(16,13),by decide⟩ := by
  change a k 14*e k 13=a k 14*1
  rw [av]
  norm_num [arrowSource]

lemma extend_131_13 : a k 13*normalRep k ⟨(13,17),by decide⟩=normalRep k ⟨(2,17),by decide⟩ := by
  change a k 13*wordValue (a k) [22] = wordValue (a k) [22, 13]
  rw [show a k 13*wordValue (a k) [22]=wordValue (a k) [22, 13] from (word_snoc (a k) [22] 13).symm]
  all_goals rfl
lemma extend_131_14 : a k 14*normalRep k ⟨(13,17),by decide⟩=normalRep k ⟨(16,17),by decide⟩ := by
  change a k 14*wordValue (a k) [22] = wordValue (a k) [21, 9]
  rw [show a k 14*wordValue (a k) [22]=wordValue (a k) [22, 14] from (word_snoc (a k) [22] 14).symm]
  calc
    wordValue (a k) [22, 14] = wordValue (a k) [21, 9] := (context_commute k 4 [] []).symm
lemma extend_132_15 : a k 15*normalRep k ⟨(14,0),by decide⟩=normalRep k ⟨(11,0),by decide⟩ := by
  change a k 15*wordValue (a k) [0, 1, 5, 8, 21, 9, 19] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6]
  rw [show a k 15*wordValue (a k) [0, 1, 5, 8, 21, 9, 19]=wordValue (a k) [0, 1, 5, 8, 21, 9, 19, 15] from (word_snoc (a k) [0, 1, 5, 8, 21, 9, 19] 15).symm]
  calc
    wordValue (a k) [0, 1, 5, 8, 21, 9, 19, 15] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6] := (context_commute k 3 [0, 1, 5, 8, 21, 9] []).symm
lemma extend_132_16 : a k 16*normalRep k ⟨(14,0),by decide⟩=normalRep k ⟨(15,0),by decide⟩ := by
  change a k 16*wordValue (a k) [0, 1, 5, 8, 21, 9, 19] = wordValue (a k) [0, 1, 5, 8, 21, 9, 19, 16]
  rw [show a k 16*wordValue (a k) [0, 1, 5, 8, 21, 9, 19]=wordValue (a k) [0, 1, 5, 8, 21, 9, 19, 16] from (word_snoc (a k) [0, 1, 5, 8, 21, 9, 19] 16).symm]
  all_goals rfl
lemma extend_133_15 : a k 15*normalRep k ⟨(14,1),by decide⟩=normalRep k ⟨(11,1),by decide⟩ := by
  change a k 15*wordValue (a k) [1, 5, 8, 21, 9, 19] = wordValue (a k) [1, 5, 8, 21, 9, 18, 6]
  rw [show a k 15*wordValue (a k) [1, 5, 8, 21, 9, 19]=wordValue (a k) [1, 5, 8, 21, 9, 19, 15] from (word_snoc (a k) [1, 5, 8, 21, 9, 19] 15).symm]
  calc
    wordValue (a k) [1, 5, 8, 21, 9, 19, 15] = wordValue (a k) [1, 5, 8, 21, 9, 18, 6] := (context_commute k 3 [1, 5, 8, 21, 9] []).symm
lemma extend_133_16 : a k 16*normalRep k ⟨(14,1),by decide⟩=normalRep k ⟨(15,1),by decide⟩ := by
  change a k 16*wordValue (a k) [1, 5, 8, 21, 9, 19] = wordValue (a k) [1, 5, 8, 21, 9, 19, 16]
  rw [show a k 16*wordValue (a k) [1, 5, 8, 21, 9, 19]=wordValue (a k) [1, 5, 8, 21, 9, 19, 16] from (word_snoc (a k) [1, 5, 8, 21, 9, 19] 16).symm]
  all_goals rfl
lemma extend_134_15 : a k 15*normalRep k ⟨(14,6),by decide⟩=normalRep k ⟨(11,6),by decide⟩ := by
  change a k 15*wordValue (a k) [5, 8, 21, 9, 19] = wordValue (a k) [5, 8, 21, 9, 18, 6]
  rw [show a k 15*wordValue (a k) [5, 8, 21, 9, 19]=wordValue (a k) [5, 8, 21, 9, 19, 15] from (word_snoc (a k) [5, 8, 21, 9, 19] 15).symm]
  calc
    wordValue (a k) [5, 8, 21, 9, 19, 15] = wordValue (a k) [5, 8, 21, 9, 18, 6] := (context_commute k 3 [5, 8, 21, 9] []).symm
lemma extend_134_16 : a k 16*normalRep k ⟨(14,6),by decide⟩=normalRep k ⟨(15,6),by decide⟩ := by
  change a k 16*wordValue (a k) [5, 8, 21, 9, 19] = wordValue (a k) [5, 8, 21, 9, 19, 16]
  rw [show a k 16*wordValue (a k) [5, 8, 21, 9, 19]=wordValue (a k) [5, 8, 21, 9, 19, 16] from (word_snoc (a k) [5, 8, 21, 9, 19] 16).symm]
  all_goals rfl
lemma extend_135_15 : a k 15*normalRep k ⟨(14,9),by decide⟩=normalRep k ⟨(11,9),by decide⟩ := by
  change a k 15*wordValue (a k) [8, 21, 9, 19] = wordValue (a k) [8, 21, 9, 18, 6]
  rw [show a k 15*wordValue (a k) [8, 21, 9, 19]=wordValue (a k) [8, 21, 9, 19, 15] from (word_snoc (a k) [8, 21, 9, 19] 15).symm]
  calc
    wordValue (a k) [8, 21, 9, 19, 15] = wordValue (a k) [8, 21, 9, 18, 6] := (context_commute k 3 [8, 21, 9] []).symm
lemma extend_135_16 : a k 16*normalRep k ⟨(14,9),by decide⟩=normalRep k ⟨(15,9),by decide⟩ := by
  change a k 16*wordValue (a k) [8, 21, 9, 19] = wordValue (a k) [8, 21, 9, 19, 16]
  rw [show a k 16*wordValue (a k) [8, 21, 9, 19]=wordValue (a k) [8, 21, 9, 19, 16] from (word_snoc (a k) [8, 21, 9, 19] 16).symm]
  all_goals rfl
lemma extend_136_15 : a k 15*normalRep k ⟨(14,10),by decide⟩=normalRep k ⟨(11,10),by decide⟩ := by
  change a k 15*wordValue (a k) [9, 19] = wordValue (a k) [9, 18, 6]
  rw [show a k 15*wordValue (a k) [9, 19]=wordValue (a k) [9, 19, 15] from (word_snoc (a k) [9, 19] 15).symm]
  calc
    wordValue (a k) [9, 19, 15] = wordValue (a k) [9, 18, 6] := (context_commute k 3 [9] []).symm
lemma extend_136_16 : a k 16*normalRep k ⟨(14,10),by decide⟩=normalRep k ⟨(15,10),by decide⟩ := by
  change a k 16*wordValue (a k) [9, 19] = wordValue (a k) [9, 19, 16]
  rw [show a k 16*wordValue (a k) [9, 19]=wordValue (a k) [9, 19, 16] from (word_snoc (a k) [9, 19] 16).symm]
  all_goals rfl
lemma extend_137_15 : a k 15*normalRep k ⟨(14,13),by decide⟩=normalRep k ⟨(11,13),by decide⟩ := by
  change a k 15*wordValue (a k) [14, 19] = wordValue (a k) [13, 2, 6]
  rw [show a k 15*wordValue (a k) [14, 19]=wordValue (a k) [14, 19, 15] from (word_snoc (a k) [14, 19] 15).symm]
  calc
    wordValue (a k) [14, 19, 15] = wordValue (a k) [14, 18, 6] := (context_commute k 3 [14] []).symm
    wordValue (a k) [14, 18, 6] = wordValue (a k) [13, 2, 6] := (context_commute k 1 [] [6]).symm
lemma extend_137_16 : a k 16*normalRep k ⟨(14,13),by decide⟩=normalRep k ⟨(15,13),by decide⟩ := by
  change a k 16*wordValue (a k) [14, 19] = wordValue (a k) [14, 19, 16]
  rw [show a k 16*wordValue (a k) [14, 19]=wordValue (a k) [14, 19, 16] from (word_snoc (a k) [14, 19] 16).symm]
  all_goals rfl
lemma extend_138_15 : a k 15*normalRep k ⟨(14,14),by decide⟩=normalRep k ⟨(11,14),by decide⟩ := by
  change a k 15*e k 14=a k 15*1
  rw [av]
  norm_num [arrowSource]

lemma extend_138_16 : a k 16*normalRep k ⟨(14,14),by decide⟩=normalRep k ⟨(15,14),by decide⟩ := by
  change a k 16*e k 14=a k 16*1
  rw [av]
  norm_num [arrowSource]

lemma extend_139_15 : a k 15*normalRep k ⟨(14,16),by decide⟩=normalRep k ⟨(11,16),by decide⟩ := by
  change a k 15*wordValue (a k) [19] = wordValue (a k) [18, 6]
  rw [show a k 15*wordValue (a k) [19]=wordValue (a k) [19, 15] from (word_snoc (a k) [19] 15).symm]
  calc
    wordValue (a k) [19, 15] = wordValue (a k) [18, 6] := (context_commute k 3 [] []).symm
lemma extend_139_16 : a k 16*normalRep k ⟨(14,16),by decide⟩=normalRep k ⟨(15,16),by decide⟩ := by
  change a k 16*wordValue (a k) [19] = wordValue (a k) [19, 16]
  rw [show a k 16*wordValue (a k) [19]=wordValue (a k) [19, 16] from (word_snoc (a k) [19] 16).symm]
  all_goals rfl
lemma extend_140_15 : a k 15*normalRep k ⟨(14,17),by decide⟩=normalRep k ⟨(11,17),by decide⟩ := by
  change a k 15*wordValue (a k) [21, 9, 19] = wordValue (a k) [21, 9, 18, 6]
  rw [show a k 15*wordValue (a k) [21, 9, 19]=wordValue (a k) [21, 9, 19, 15] from (word_snoc (a k) [21, 9, 19] 15).symm]
  calc
    wordValue (a k) [21, 9, 19, 15] = wordValue (a k) [21, 9, 18, 6] := (context_commute k 3 [21, 9] []).symm
lemma extend_140_16 : a k 16*normalRep k ⟨(14,17),by decide⟩=normalRep k ⟨(15,17),by decide⟩ := by
  change a k 16*wordValue (a k) [21, 9, 19] = wordValue (a k) [21, 9, 19, 16]
  rw [show a k 16*wordValue (a k) [21, 9, 19]=wordValue (a k) [21, 9, 19, 16] from (word_snoc (a k) [21, 9, 19] 16).symm]
  all_goals rfl
lemma extend_141_17 : a k 17*normalRep k ⟨(15,0),by decide⟩=normalRep k ⟨(12,0),by decide⟩ := by
  change a k 17*wordValue (a k) [0, 1, 5, 8, 21, 9, 19, 16] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 11]
  rw [show a k 17*wordValue (a k) [0, 1, 5, 8, 21, 9, 19, 16]=wordValue (a k) [0, 1, 5, 8, 21, 9, 19, 16, 17] from (word_snoc (a k) [0, 1, 5, 8, 21, 9, 19, 16] 17).symm]
  calc
    wordValue (a k) [0, 1, 5, 8, 21, 9, 19, 16, 17] = wordValue (a k) [0, 1, 5, 8, 21, 9, 19, 15, 11] := (context_commute k 2 [0, 1, 5, 8, 21, 9, 19] []).symm
    wordValue (a k) [0, 1, 5, 8, 21, 9, 19, 15, 11] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 11] := (context_commute k 3 [0, 1, 5, 8, 21, 9] [11]).symm
lemma extend_142_17 : a k 17*normalRep k ⟨(15,1),by decide⟩=normalRep k ⟨(12,1),by decide⟩ := by
  change a k 17*wordValue (a k) [1, 5, 8, 21, 9, 19, 16] = wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 11]
  rw [show a k 17*wordValue (a k) [1, 5, 8, 21, 9, 19, 16]=wordValue (a k) [1, 5, 8, 21, 9, 19, 16, 17] from (word_snoc (a k) [1, 5, 8, 21, 9, 19, 16] 17).symm]
  calc
    wordValue (a k) [1, 5, 8, 21, 9, 19, 16, 17] = wordValue (a k) [1, 5, 8, 21, 9, 19, 15, 11] := (context_commute k 2 [1, 5, 8, 21, 9, 19] []).symm
    wordValue (a k) [1, 5, 8, 21, 9, 19, 15, 11] = wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 11] := (context_commute k 3 [1, 5, 8, 21, 9] [11]).symm
lemma extend_143_17 : a k 17*normalRep k ⟨(15,6),by decide⟩=normalRep k ⟨(12,6),by decide⟩ := by
  change a k 17*wordValue (a k) [5, 8, 21, 9, 19, 16] = wordValue (a k) [5, 8, 21, 9, 18, 6, 11]
  rw [show a k 17*wordValue (a k) [5, 8, 21, 9, 19, 16]=wordValue (a k) [5, 8, 21, 9, 19, 16, 17] from (word_snoc (a k) [5, 8, 21, 9, 19, 16] 17).symm]
  calc
    wordValue (a k) [5, 8, 21, 9, 19, 16, 17] = wordValue (a k) [5, 8, 21, 9, 19, 15, 11] := (context_commute k 2 [5, 8, 21, 9, 19] []).symm
    wordValue (a k) [5, 8, 21, 9, 19, 15, 11] = wordValue (a k) [5, 8, 21, 9, 18, 6, 11] := (context_commute k 3 [5, 8, 21, 9] [11]).symm
lemma extend_144_17 : a k 17*normalRep k ⟨(15,9),by decide⟩=normalRep k ⟨(12,9),by decide⟩ := by
  change a k 17*wordValue (a k) [8, 21, 9, 19, 16] = wordValue (a k) [8, 21, 9, 18, 6, 11]
  rw [show a k 17*wordValue (a k) [8, 21, 9, 19, 16]=wordValue (a k) [8, 21, 9, 19, 16, 17] from (word_snoc (a k) [8, 21, 9, 19, 16] 17).symm]
  calc
    wordValue (a k) [8, 21, 9, 19, 16, 17] = wordValue (a k) [8, 21, 9, 19, 15, 11] := (context_commute k 2 [8, 21, 9, 19] []).symm
    wordValue (a k) [8, 21, 9, 19, 15, 11] = wordValue (a k) [8, 21, 9, 18, 6, 11] := (context_commute k 3 [8, 21, 9] [11]).symm
lemma extend_145_17 : a k 17*normalRep k ⟨(15,10),by decide⟩=normalRep k ⟨(12,10),by decide⟩ := by
  change a k 17*wordValue (a k) [9, 19, 16] = wordValue (a k) [9, 18, 6, 11]
  rw [show a k 17*wordValue (a k) [9, 19, 16]=wordValue (a k) [9, 19, 16, 17] from (word_snoc (a k) [9, 19, 16] 17).symm]
  calc
    wordValue (a k) [9, 19, 16, 17] = wordValue (a k) [9, 19, 15, 11] := (context_commute k 2 [9, 19] []).symm
    wordValue (a k) [9, 19, 15, 11] = wordValue (a k) [9, 18, 6, 11] := (context_commute k 3 [9] [11]).symm
lemma extend_146_17 : a k 17*normalRep k ⟨(15,13),by decide⟩=normalRep k ⟨(12,13),by decide⟩ := by
  change a k 17*wordValue (a k) [14, 19, 16] = wordValue (a k) [13, 2, 6, 11]
  rw [show a k 17*wordValue (a k) [14, 19, 16]=wordValue (a k) [14, 19, 16, 17] from (word_snoc (a k) [14, 19, 16] 17).symm]
  calc
    wordValue (a k) [14, 19, 16, 17] = wordValue (a k) [14, 19, 15, 11] := (context_commute k 2 [14, 19] []).symm
    wordValue (a k) [14, 19, 15, 11] = wordValue (a k) [14, 18, 6, 11] := (context_commute k 3 [14] [11]).symm
    wordValue (a k) [14, 18, 6, 11] = wordValue (a k) [13, 2, 6, 11] := (context_commute k 1 [] [6, 11]).symm
lemma extend_147_17 : a k 17*normalRep k ⟨(15,14),by decide⟩=normalRep k ⟨(12,14),by decide⟩ := by
  change a k 17*wordValue (a k) [16] = wordValue (a k) [15, 11]
  rw [show a k 17*wordValue (a k) [16]=wordValue (a k) [16, 17] from (word_snoc (a k) [16] 17).symm]
  calc
    wordValue (a k) [16, 17] = wordValue (a k) [15, 11] := (context_commute k 2 [] []).symm
lemma extend_148_17 : a k 17*normalRep k ⟨(15,15),by decide⟩=normalRep k ⟨(12,15),by decide⟩ := by
  change a k 17*e k 15=a k 17*1
  rw [av]
  norm_num [arrowSource]

lemma extend_149_17 : a k 17*normalRep k ⟨(15,16),by decide⟩=normalRep k ⟨(12,16),by decide⟩ := by
  change a k 17*wordValue (a k) [19, 16] = wordValue (a k) [18, 6, 11]
  rw [show a k 17*wordValue (a k) [19, 16]=wordValue (a k) [19, 16, 17] from (word_snoc (a k) [19, 16] 17).symm]
  calc
    wordValue (a k) [19, 16, 17] = wordValue (a k) [19, 15, 11] := (context_commute k 2 [19] []).symm
    wordValue (a k) [19, 15, 11] = wordValue (a k) [18, 6, 11] := (context_commute k 3 [] [11]).symm
lemma extend_150_17 : a k 17*normalRep k ⟨(15,17),by decide⟩=normalRep k ⟨(12,17),by decide⟩ := by
  change a k 17*wordValue (a k) [21, 9, 19, 16] = wordValue (a k) [21, 9, 18, 6, 11]
  rw [show a k 17*wordValue (a k) [21, 9, 19, 16]=wordValue (a k) [21, 9, 19, 16, 17] from (word_snoc (a k) [21, 9, 19, 16] 17).symm]
  calc
    wordValue (a k) [21, 9, 19, 16, 17] = wordValue (a k) [21, 9, 19, 15, 11] := (context_commute k 2 [21, 9, 19] []).symm
    wordValue (a k) [21, 9, 19, 15, 11] = wordValue (a k) [21, 9, 18, 6, 11] := (context_commute k 3 [21, 9] [11]).symm
lemma extend_151_18 : a k 18*normalRep k ⟨(16,0),by decide⟩=normalRep k ⟨(7,0),by decide⟩ := by
  change a k 18*wordValue (a k) [0, 1, 5, 8, 21, 9] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18]
  rw [show a k 18*wordValue (a k) [0, 1, 5, 8, 21, 9]=wordValue (a k) [0, 1, 5, 8, 21, 9, 18] from (word_snoc (a k) [0, 1, 5, 8, 21, 9] 18).symm]
  all_goals rfl
lemma extend_151_19 : a k 19*normalRep k ⟨(16,0),by decide⟩=normalRep k ⟨(14,0),by decide⟩ := by
  change a k 19*wordValue (a k) [0, 1, 5, 8, 21, 9] = wordValue (a k) [0, 1, 5, 8, 21, 9, 19]
  rw [show a k 19*wordValue (a k) [0, 1, 5, 8, 21, 9]=wordValue (a k) [0, 1, 5, 8, 21, 9, 19] from (word_snoc (a k) [0, 1, 5, 8, 21, 9] 19).symm]
  all_goals rfl
lemma extend_152_18 : a k 18*normalRep k ⟨(16,1),by decide⟩=normalRep k ⟨(7,1),by decide⟩ := by
  change a k 18*wordValue (a k) [1, 5, 8, 21, 9] = wordValue (a k) [1, 5, 8, 21, 9, 18]
  rw [show a k 18*wordValue (a k) [1, 5, 8, 21, 9]=wordValue (a k) [1, 5, 8, 21, 9, 18] from (word_snoc (a k) [1, 5, 8, 21, 9] 18).symm]
  all_goals rfl
lemma extend_152_19 : a k 19*normalRep k ⟨(16,1),by decide⟩=normalRep k ⟨(14,1),by decide⟩ := by
  change a k 19*wordValue (a k) [1, 5, 8, 21, 9] = wordValue (a k) [1, 5, 8, 21, 9, 19]
  rw [show a k 19*wordValue (a k) [1, 5, 8, 21, 9]=wordValue (a k) [1, 5, 8, 21, 9, 19] from (word_snoc (a k) [1, 5, 8, 21, 9] 19).symm]
  all_goals rfl
lemma extend_153_18 : a k 18*normalRep k ⟨(16,6),by decide⟩=normalRep k ⟨(7,6),by decide⟩ := by
  change a k 18*wordValue (a k) [5, 8, 21, 9] = wordValue (a k) [5, 8, 21, 9, 18]
  rw [show a k 18*wordValue (a k) [5, 8, 21, 9]=wordValue (a k) [5, 8, 21, 9, 18] from (word_snoc (a k) [5, 8, 21, 9] 18).symm]
  all_goals rfl
lemma extend_153_19 : a k 19*normalRep k ⟨(16,6),by decide⟩=normalRep k ⟨(14,6),by decide⟩ := by
  change a k 19*wordValue (a k) [5, 8, 21, 9] = wordValue (a k) [5, 8, 21, 9, 19]
  rw [show a k 19*wordValue (a k) [5, 8, 21, 9]=wordValue (a k) [5, 8, 21, 9, 19] from (word_snoc (a k) [5, 8, 21, 9] 19).symm]
  all_goals rfl
lemma extend_154_18 : a k 18*normalRep k ⟨(16,9),by decide⟩=normalRep k ⟨(7,9),by decide⟩ := by
  change a k 18*wordValue (a k) [8, 21, 9] = wordValue (a k) [8, 21, 9, 18]
  rw [show a k 18*wordValue (a k) [8, 21, 9]=wordValue (a k) [8, 21, 9, 18] from (word_snoc (a k) [8, 21, 9] 18).symm]
  all_goals rfl
lemma extend_154_19 : a k 19*normalRep k ⟨(16,9),by decide⟩=normalRep k ⟨(14,9),by decide⟩ := by
  change a k 19*wordValue (a k) [8, 21, 9] = wordValue (a k) [8, 21, 9, 19]
  rw [show a k 19*wordValue (a k) [8, 21, 9]=wordValue (a k) [8, 21, 9, 19] from (word_snoc (a k) [8, 21, 9] 19).symm]
  all_goals rfl
lemma extend_155_18 : a k 18*normalRep k ⟨(16,10),by decide⟩=normalRep k ⟨(7,10),by decide⟩ := by
  change a k 18*wordValue (a k) [9] = wordValue (a k) [9, 18]
  rw [show a k 18*wordValue (a k) [9]=wordValue (a k) [9, 18] from (word_snoc (a k) [9] 18).symm]
  all_goals rfl
lemma extend_155_19 : a k 19*normalRep k ⟨(16,10),by decide⟩=normalRep k ⟨(14,10),by decide⟩ := by
  change a k 19*wordValue (a k) [9] = wordValue (a k) [9, 19]
  rw [show a k 19*wordValue (a k) [9]=wordValue (a k) [9, 19] from (word_snoc (a k) [9] 19).symm]
  all_goals rfl
lemma extend_156_18 : a k 18*normalRep k ⟨(16,13),by decide⟩=normalRep k ⟨(7,13),by decide⟩ := by
  change a k 18*wordValue (a k) [14] = wordValue (a k) [13, 2]
  rw [show a k 18*wordValue (a k) [14]=wordValue (a k) [14, 18] from (word_snoc (a k) [14] 18).symm]
  calc
    wordValue (a k) [14, 18] = wordValue (a k) [13, 2] := (context_commute k 1 [] []).symm
lemma extend_156_19 : a k 19*normalRep k ⟨(16,13),by decide⟩=normalRep k ⟨(14,13),by decide⟩ := by
  change a k 19*wordValue (a k) [14] = wordValue (a k) [14, 19]
  rw [show a k 19*wordValue (a k) [14]=wordValue (a k) [14, 19] from (word_snoc (a k) [14] 19).symm]
  all_goals rfl
lemma extend_157_18 : a k 18*normalRep k ⟨(16,16),by decide⟩=normalRep k ⟨(7,16),by decide⟩ := by
  change a k 18*e k 16=a k 18*1
  rw [av]
  norm_num [arrowSource]

lemma extend_157_19 : a k 19*normalRep k ⟨(16,16),by decide⟩=normalRep k ⟨(14,16),by decide⟩ := by
  change a k 19*e k 16=a k 19*1
  rw [av]
  norm_num [arrowSource]

lemma extend_158_18 : a k 18*normalRep k ⟨(16,17),by decide⟩=normalRep k ⟨(7,17),by decide⟩ := by
  change a k 18*wordValue (a k) [21, 9] = wordValue (a k) [21, 9, 18]
  rw [show a k 18*wordValue (a k) [21, 9]=wordValue (a k) [21, 9, 18] from (word_snoc (a k) [21, 9] 18).symm]
  all_goals rfl
lemma extend_158_19 : a k 19*normalRep k ⟨(16,17),by decide⟩=normalRep k ⟨(14,17),by decide⟩ := by
  change a k 19*wordValue (a k) [21, 9] = wordValue (a k) [21, 9, 19]
  rw [show a k 19*wordValue (a k) [21, 9]=wordValue (a k) [21, 9, 19] from (word_snoc (a k) [21, 9] 19).symm]
  all_goals rfl
lemma extend_159_20 : a k 20*normalRep k ⟨(17,0),by decide⟩=0 := by
  change a k 20*wordValue (a k) [0, 1, 5, 8] = 0
  rw [show a k 20*wordValue (a k) [0, 1, 5, 8]=wordValue (a k) [0, 1, 5, 8, 20] from (word_snoc (a k) [0, 1, 5, 8] 20).symm]
  calc
    wordValue (a k) [0, 1, 5, 8, 20] = 0 := context_zero k 2 [0, 1, 5] []
lemma extend_159_21 : a k 21*normalRep k ⟨(17,0),by decide⟩=normalRep k ⟨(10,0),by decide⟩ := by
  change a k 21*wordValue (a k) [0, 1, 5, 8] = wordValue (a k) [0, 1, 5, 8, 21]
  rw [show a k 21*wordValue (a k) [0, 1, 5, 8]=wordValue (a k) [0, 1, 5, 8, 21] from (word_snoc (a k) [0, 1, 5, 8] 21).symm]
  all_goals rfl
lemma extend_159_22 : a k 22*normalRep k ⟨(17,0),by decide⟩=normalRep k ⟨(13,0),by decide⟩ := by
  change a k 22*wordValue (a k) [0, 1, 5, 8] = wordValue (a k) [0, 1, 5, 8, 22]
  rw [show a k 22*wordValue (a k) [0, 1, 5, 8]=wordValue (a k) [0, 1, 5, 8, 22] from (word_snoc (a k) [0, 1, 5, 8] 22).symm]
  all_goals rfl
lemma extend_160_20 : a k 20*normalRep k ⟨(17,1),by decide⟩=0 := by
  change a k 20*wordValue (a k) [1, 5, 8] = 0
  rw [show a k 20*wordValue (a k) [1, 5, 8]=wordValue (a k) [1, 5, 8, 20] from (word_snoc (a k) [1, 5, 8] 20).symm]
  calc
    wordValue (a k) [1, 5, 8, 20] = 0 := context_zero k 2 [1, 5] []
lemma extend_160_21 : a k 21*normalRep k ⟨(17,1),by decide⟩=normalRep k ⟨(10,1),by decide⟩ := by
  change a k 21*wordValue (a k) [1, 5, 8] = wordValue (a k) [1, 5, 8, 21]
  rw [show a k 21*wordValue (a k) [1, 5, 8]=wordValue (a k) [1, 5, 8, 21] from (word_snoc (a k) [1, 5, 8] 21).symm]
  all_goals rfl
lemma extend_160_22 : a k 22*normalRep k ⟨(17,1),by decide⟩=normalRep k ⟨(13,1),by decide⟩ := by
  change a k 22*wordValue (a k) [1, 5, 8] = wordValue (a k) [1, 5, 8, 22]
  rw [show a k 22*wordValue (a k) [1, 5, 8]=wordValue (a k) [1, 5, 8, 22] from (word_snoc (a k) [1, 5, 8] 22).symm]
  all_goals rfl
lemma extend_161_20 : a k 20*normalRep k ⟨(17,6),by decide⟩=0 := by
  change a k 20*wordValue (a k) [5, 8] = 0
  rw [show a k 20*wordValue (a k) [5, 8]=wordValue (a k) [5, 8, 20] from (word_snoc (a k) [5, 8] 20).symm]
  calc
    wordValue (a k) [5, 8, 20] = 0 := context_zero k 2 [5] []
lemma extend_161_21 : a k 21*normalRep k ⟨(17,6),by decide⟩=normalRep k ⟨(10,6),by decide⟩ := by
  change a k 21*wordValue (a k) [5, 8] = wordValue (a k) [5, 8, 21]
  rw [show a k 21*wordValue (a k) [5, 8]=wordValue (a k) [5, 8, 21] from (word_snoc (a k) [5, 8] 21).symm]
  all_goals rfl
lemma extend_161_22 : a k 22*normalRep k ⟨(17,6),by decide⟩=normalRep k ⟨(13,6),by decide⟩ := by
  change a k 22*wordValue (a k) [5, 8] = wordValue (a k) [5, 8, 22]
  rw [show a k 22*wordValue (a k) [5, 8]=wordValue (a k) [5, 8, 22] from (word_snoc (a k) [5, 8] 22).symm]
  all_goals rfl
lemma extend_162_20 : a k 20*normalRep k ⟨(17,9),by decide⟩=0 := by
  change a k 20*wordValue (a k) [8] = 0
  rw [show a k 20*wordValue (a k) [8]=wordValue (a k) [8, 20] from (word_snoc (a k) [8] 20).symm]
  calc
    wordValue (a k) [8, 20] = 0 := context_zero k 2 [] []
lemma extend_162_21 : a k 21*normalRep k ⟨(17,9),by decide⟩=normalRep k ⟨(10,9),by decide⟩ := by
  change a k 21*wordValue (a k) [8] = wordValue (a k) [8, 21]
  rw [show a k 21*wordValue (a k) [8]=wordValue (a k) [8, 21] from (word_snoc (a k) [8] 21).symm]
  all_goals rfl
lemma extend_162_22 : a k 22*normalRep k ⟨(17,9),by decide⟩=normalRep k ⟨(13,9),by decide⟩ := by
  change a k 22*wordValue (a k) [8] = wordValue (a k) [8, 22]
  rw [show a k 22*wordValue (a k) [8]=wordValue (a k) [8, 22] from (word_snoc (a k) [8] 22).symm]
  all_goals rfl
lemma extend_163_20 : a k 20*normalRep k ⟨(17,17),by decide⟩=normalRep k ⟨(8,18),by decide⟩ := by
  change a k 20*e k 17=a k 20*1
  rw [av]
  norm_num [arrowSource]

lemma extend_163_21 : a k 21*normalRep k ⟨(17,17),by decide⟩=normalRep k ⟨(10,17),by decide⟩ := by
  change a k 21*e k 17=a k 21*1
  rw [av]
  norm_num [arrowSource]

lemma extend_163_22 : a k 22*normalRep k ⟨(17,17),by decide⟩=normalRep k ⟨(13,17),by decide⟩ := by
  change a k 22*e k 17=a k 22*1
  rw [av]
  norm_num [arrowSource]

lemma extend_164_20 : a k 20*normalRep k ⟨(18,0),by decide⟩=normalRep k ⟨(8,0),by decide⟩ := by
  change a k 20*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3] = wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20]
  rw [show a k 20*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3]=wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 20] from (word_snoc (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3] 20).symm]
  all_goals rfl
lemma extend_164_21 : a k 21*normalRep k ⟨(18,0),by decide⟩=0 := by
  change a k 21*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3] = 0
  rw [show a k 21*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3]=wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 21] from (word_snoc (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3] 21).symm]
  calc
    wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 21] = 0 := context_zero k 0 [0, 1, 5, 8, 21, 9, 18, 6, 10] []
lemma extend_164_22 : a k 22*normalRep k ⟨(18,0),by decide⟩=0 := by
  change a k 22*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3] = 0
  rw [show a k 22*wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3]=wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 22] from (word_snoc (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3] 22).symm]
  calc
    wordValue (a k) [0, 1, 5, 8, 21, 9, 18, 6, 10, 3, 22] = 0 := context_zero k 1 [0, 1, 5, 8, 21, 9, 18, 6, 10] []
lemma extend_165_20 : a k 20*normalRep k ⟨(18,1),by decide⟩=normalRep k ⟨(8,1),by decide⟩ := by
  change a k 20*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3] = wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 20]
  rw [show a k 20*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3]=wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 20] from (word_snoc (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3] 20).symm]
  all_goals rfl
lemma extend_165_21 : a k 21*normalRep k ⟨(18,1),by decide⟩=0 := by
  change a k 21*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3] = 0
  rw [show a k 21*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3]=wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 21] from (word_snoc (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3] 21).symm]
  calc
    wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 21] = 0 := context_zero k 0 [1, 5, 8, 21, 9, 18, 6, 10] []
lemma extend_165_22 : a k 22*normalRep k ⟨(18,1),by decide⟩=0 := by
  change a k 22*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3] = 0
  rw [show a k 22*wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3]=wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 22] from (word_snoc (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3] 22).symm]
  calc
    wordValue (a k) [1, 5, 8, 21, 9, 18, 6, 10, 3, 22] = 0 := context_zero k 1 [1, 5, 8, 21, 9, 18, 6, 10] []
lemma extend_166_20 : a k 20*normalRep k ⟨(18,2),by decide⟩=normalRep k ⟨(8,2),by decide⟩ := by
  change a k 20*wordValue (a k) [2, 6, 10, 3] = wordValue (a k) [2, 6, 10, 3, 20]
  rw [show a k 20*wordValue (a k) [2, 6, 10, 3]=wordValue (a k) [2, 6, 10, 3, 20] from (word_snoc (a k) [2, 6, 10, 3] 20).symm]
  all_goals rfl
lemma extend_166_21 : a k 21*normalRep k ⟨(18,2),by decide⟩=0 := by
  change a k 21*wordValue (a k) [2, 6, 10, 3] = 0
  rw [show a k 21*wordValue (a k) [2, 6, 10, 3]=wordValue (a k) [2, 6, 10, 3, 21] from (word_snoc (a k) [2, 6, 10, 3] 21).symm]
  calc
    wordValue (a k) [2, 6, 10, 3, 21] = 0 := context_zero k 0 [2, 6, 10] []
lemma extend_166_22 : a k 22*normalRep k ⟨(18,2),by decide⟩=0 := by
  change a k 22*wordValue (a k) [2, 6, 10, 3] = 0
  rw [show a k 22*wordValue (a k) [2, 6, 10, 3]=wordValue (a k) [2, 6, 10, 3, 22] from (word_snoc (a k) [2, 6, 10, 3] 22).symm]
  calc
    wordValue (a k) [2, 6, 10, 3, 22] = 0 := context_zero k 1 [2, 6, 10] []
lemma extend_167_20 : a k 20*normalRep k ⟨(18,3),by decide⟩=normalRep k ⟨(8,3),by decide⟩ := by
  change a k 20*wordValue (a k) [3] = wordValue (a k) [3, 20]
  rw [show a k 20*wordValue (a k) [3]=wordValue (a k) [3, 20] from (word_snoc (a k) [3] 20).symm]
  all_goals rfl
lemma extend_167_21 : a k 21*normalRep k ⟨(18,3),by decide⟩=0 := by
  change a k 21*wordValue (a k) [3] = 0
  rw [show a k 21*wordValue (a k) [3]=wordValue (a k) [3, 21] from (word_snoc (a k) [3] 21).symm]
  calc
    wordValue (a k) [3, 21] = 0 := context_zero k 0 [] []
lemma extend_167_22 : a k 22*normalRep k ⟨(18,3),by decide⟩=0 := by
  change a k 22*wordValue (a k) [3] = 0
  rw [show a k 22*wordValue (a k) [3]=wordValue (a k) [3, 22] from (word_snoc (a k) [3] 22).symm]
  calc
    wordValue (a k) [3, 22] = 0 := context_zero k 1 [] []
lemma extend_168_20 : a k 20*normalRep k ⟨(18,6),by decide⟩=normalRep k ⟨(8,6),by decide⟩ := by
  change a k 20*wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3] = wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 20]
  rw [show a k 20*wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3]=wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 20] from (word_snoc (a k) [5, 8, 21, 9, 18, 6, 10, 3] 20).symm]
  all_goals rfl
lemma extend_168_21 : a k 21*normalRep k ⟨(18,6),by decide⟩=0 := by
  change a k 21*wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3] = 0
  rw [show a k 21*wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3]=wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 21] from (word_snoc (a k) [5, 8, 21, 9, 18, 6, 10, 3] 21).symm]
  calc
    wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 21] = 0 := context_zero k 0 [5, 8, 21, 9, 18, 6, 10] []
lemma extend_168_22 : a k 22*normalRep k ⟨(18,6),by decide⟩=0 := by
  change a k 22*wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3] = 0
  rw [show a k 22*wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3]=wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 22] from (word_snoc (a k) [5, 8, 21, 9, 18, 6, 10, 3] 22).symm]
  calc
    wordValue (a k) [5, 8, 21, 9, 18, 6, 10, 3, 22] = 0 := context_zero k 1 [5, 8, 21, 9, 18, 6, 10] []
lemma extend_169_20 : a k 20*normalRep k ⟨(18,7),by decide⟩=normalRep k ⟨(8,7),by decide⟩ := by
  change a k 20*wordValue (a k) [6, 10, 3] = wordValue (a k) [6, 10, 3, 20]
  rw [show a k 20*wordValue (a k) [6, 10, 3]=wordValue (a k) [6, 10, 3, 20] from (word_snoc (a k) [6, 10, 3] 20).symm]
  all_goals rfl
lemma extend_169_21 : a k 21*normalRep k ⟨(18,7),by decide⟩=0 := by
  change a k 21*wordValue (a k) [6, 10, 3] = 0
  rw [show a k 21*wordValue (a k) [6, 10, 3]=wordValue (a k) [6, 10, 3, 21] from (word_snoc (a k) [6, 10, 3] 21).symm]
  calc
    wordValue (a k) [6, 10, 3, 21] = 0 := context_zero k 0 [6, 10] []
lemma extend_169_22 : a k 22*normalRep k ⟨(18,7),by decide⟩=0 := by
  change a k 22*wordValue (a k) [6, 10, 3] = 0
  rw [show a k 22*wordValue (a k) [6, 10, 3]=wordValue (a k) [6, 10, 3, 22] from (word_snoc (a k) [6, 10, 3] 22).symm]
  calc
    wordValue (a k) [6, 10, 3, 22] = 0 := context_zero k 1 [6, 10] []
lemma extend_170_20 : a k 20*normalRep k ⟨(18,9),by decide⟩=normalRep k ⟨(8,9),by decide⟩ := by
  change a k 20*wordValue (a k) [8, 21, 9, 18, 6, 10, 3] = wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 20]
  rw [show a k 20*wordValue (a k) [8, 21, 9, 18, 6, 10, 3]=wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 20] from (word_snoc (a k) [8, 21, 9, 18, 6, 10, 3] 20).symm]
  all_goals rfl
lemma extend_170_21 : a k 21*normalRep k ⟨(18,9),by decide⟩=0 := by
  change a k 21*wordValue (a k) [8, 21, 9, 18, 6, 10, 3] = 0
  rw [show a k 21*wordValue (a k) [8, 21, 9, 18, 6, 10, 3]=wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 21] from (word_snoc (a k) [8, 21, 9, 18, 6, 10, 3] 21).symm]
  calc
    wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 21] = 0 := context_zero k 0 [8, 21, 9, 18, 6, 10] []
lemma extend_170_22 : a k 22*normalRep k ⟨(18,9),by decide⟩=0 := by
  change a k 22*wordValue (a k) [8, 21, 9, 18, 6, 10, 3] = 0
  rw [show a k 22*wordValue (a k) [8, 21, 9, 18, 6, 10, 3]=wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 22] from (word_snoc (a k) [8, 21, 9, 18, 6, 10, 3] 22).symm]
  calc
    wordValue (a k) [8, 21, 9, 18, 6, 10, 3, 22] = 0 := context_zero k 1 [8, 21, 9, 18, 6, 10] []
lemma extend_171_20 : a k 20*normalRep k ⟨(18,10),by decide⟩=normalRep k ⟨(8,10),by decide⟩ := by
  change a k 20*wordValue (a k) [9, 18, 6, 10, 3] = wordValue (a k) [9, 18, 6, 10, 3, 20]
  rw [show a k 20*wordValue (a k) [9, 18, 6, 10, 3]=wordValue (a k) [9, 18, 6, 10, 3, 20] from (word_snoc (a k) [9, 18, 6, 10, 3] 20).symm]
  all_goals rfl
lemma extend_171_21 : a k 21*normalRep k ⟨(18,10),by decide⟩=0 := by
  change a k 21*wordValue (a k) [9, 18, 6, 10, 3] = 0
  rw [show a k 21*wordValue (a k) [9, 18, 6, 10, 3]=wordValue (a k) [9, 18, 6, 10, 3, 21] from (word_snoc (a k) [9, 18, 6, 10, 3] 21).symm]
  calc
    wordValue (a k) [9, 18, 6, 10, 3, 21] = 0 := context_zero k 0 [9, 18, 6, 10] []
lemma extend_171_22 : a k 22*normalRep k ⟨(18,10),by decide⟩=0 := by
  change a k 22*wordValue (a k) [9, 18, 6, 10, 3] = 0
  rw [show a k 22*wordValue (a k) [9, 18, 6, 10, 3]=wordValue (a k) [9, 18, 6, 10, 3, 22] from (word_snoc (a k) [9, 18, 6, 10, 3] 22).symm]
  calc
    wordValue (a k) [9, 18, 6, 10, 3, 22] = 0 := context_zero k 1 [9, 18, 6, 10] []
lemma extend_172_20 : a k 20*normalRep k ⟨(18,11),by decide⟩=normalRep k ⟨(8,11),by decide⟩ := by
  change a k 20*wordValue (a k) [10, 3] = wordValue (a k) [10, 3, 20]
  rw [show a k 20*wordValue (a k) [10, 3]=wordValue (a k) [10, 3, 20] from (word_snoc (a k) [10, 3] 20).symm]
  all_goals rfl
lemma extend_172_21 : a k 21*normalRep k ⟨(18,11),by decide⟩=0 := by
  change a k 21*wordValue (a k) [10, 3] = 0
  rw [show a k 21*wordValue (a k) [10, 3]=wordValue (a k) [10, 3, 21] from (word_snoc (a k) [10, 3] 21).symm]
  calc
    wordValue (a k) [10, 3, 21] = 0 := context_zero k 0 [10] []
lemma extend_172_22 : a k 22*normalRep k ⟨(18,11),by decide⟩=0 := by
  change a k 22*wordValue (a k) [10, 3] = 0
  rw [show a k 22*wordValue (a k) [10, 3]=wordValue (a k) [10, 3, 22] from (word_snoc (a k) [10, 3] 22).symm]
  calc
    wordValue (a k) [10, 3, 22] = 0 := context_zero k 1 [10] []
lemma extend_173_20 : a k 20*normalRep k ⟨(18,12),by decide⟩=normalRep k ⟨(8,12),by decide⟩ := by
  change a k 20*wordValue (a k) [12] = wordValue (a k) [12, 20]
  rw [show a k 20*wordValue (a k) [12]=wordValue (a k) [12, 20] from (word_snoc (a k) [12] 20).symm]
  all_goals rfl
lemma extend_173_21 : a k 21*normalRep k ⟨(18,12),by decide⟩=0 := by
  change a k 21*wordValue (a k) [12] = 0
  rw [show a k 21*wordValue (a k) [12]=wordValue (a k) [12, 21] from (word_snoc (a k) [12] 21).symm]
  calc
    wordValue (a k) [12, 21] = 0 := context_zero k 3 [] []
lemma extend_173_22 : a k 22*normalRep k ⟨(18,12),by decide⟩=0 := by
  change a k 22*wordValue (a k) [12] = 0
  rw [show a k 22*wordValue (a k) [12]=wordValue (a k) [12, 22] from (word_snoc (a k) [12] 22).symm]
  calc
    wordValue (a k) [12, 22] = 0 := context_zero k 4 [] []
lemma extend_174_20 : a k 20*normalRep k ⟨(18,13),by decide⟩=normalRep k ⟨(8,13),by decide⟩ := by
  change a k 20*wordValue (a k) [13, 2, 6, 10, 3] = wordValue (a k) [13, 2, 6, 10, 3, 20]
  rw [show a k 20*wordValue (a k) [13, 2, 6, 10, 3]=wordValue (a k) [13, 2, 6, 10, 3, 20] from (word_snoc (a k) [13, 2, 6, 10, 3] 20).symm]
  all_goals rfl
lemma extend_174_21 : a k 21*normalRep k ⟨(18,13),by decide⟩=0 := by
  change a k 21*wordValue (a k) [13, 2, 6, 10, 3] = 0
  rw [show a k 21*wordValue (a k) [13, 2, 6, 10, 3]=wordValue (a k) [13, 2, 6, 10, 3, 21] from (word_snoc (a k) [13, 2, 6, 10, 3] 21).symm]
  calc
    wordValue (a k) [13, 2, 6, 10, 3, 21] = 0 := context_zero k 0 [13, 2, 6, 10] []
lemma extend_174_22 : a k 22*normalRep k ⟨(18,13),by decide⟩=0 := by
  change a k 22*wordValue (a k) [13, 2, 6, 10, 3] = 0
  rw [show a k 22*wordValue (a k) [13, 2, 6, 10, 3]=wordValue (a k) [13, 2, 6, 10, 3, 22] from (word_snoc (a k) [13, 2, 6, 10, 3] 22).symm]
  calc
    wordValue (a k) [13, 2, 6, 10, 3, 22] = 0 := context_zero k 1 [13, 2, 6, 10] []
lemma extend_175_20 : a k 20*normalRep k ⟨(18,14),by decide⟩=normalRep k ⟨(8,14),by decide⟩ := by
  change a k 20*wordValue (a k) [15, 10, 3] = wordValue (a k) [15, 10, 3, 20]
  rw [show a k 20*wordValue (a k) [15, 10, 3]=wordValue (a k) [15, 10, 3, 20] from (word_snoc (a k) [15, 10, 3] 20).symm]
  all_goals rfl
lemma extend_175_21 : a k 21*normalRep k ⟨(18,14),by decide⟩=0 := by
  change a k 21*wordValue (a k) [15, 10, 3] = 0
  rw [show a k 21*wordValue (a k) [15, 10, 3]=wordValue (a k) [15, 10, 3, 21] from (word_snoc (a k) [15, 10, 3] 21).symm]
  calc
    wordValue (a k) [15, 10, 3, 21] = 0 := context_zero k 0 [15, 10] []
lemma extend_175_22 : a k 22*normalRep k ⟨(18,14),by decide⟩=0 := by
  change a k 22*wordValue (a k) [15, 10, 3] = 0
  rw [show a k 22*wordValue (a k) [15, 10, 3]=wordValue (a k) [15, 10, 3, 22] from (word_snoc (a k) [15, 10, 3] 22).symm]
  calc
    wordValue (a k) [15, 10, 3, 22] = 0 := context_zero k 1 [15, 10] []
lemma extend_176_20 : a k 20*normalRep k ⟨(18,15),by decide⟩=normalRep k ⟨(8,15),by decide⟩ := by
  change a k 20*wordValue (a k) [17, 12] = wordValue (a k) [17, 12, 20]
  rw [show a k 20*wordValue (a k) [17, 12]=wordValue (a k) [17, 12, 20] from (word_snoc (a k) [17, 12] 20).symm]
  all_goals rfl
lemma extend_176_21 : a k 21*normalRep k ⟨(18,15),by decide⟩=0 := by
  change a k 21*wordValue (a k) [17, 12] = 0
  rw [show a k 21*wordValue (a k) [17, 12]=wordValue (a k) [17, 12, 21] from (word_snoc (a k) [17, 12] 21).symm]
  calc
    wordValue (a k) [17, 12, 21] = 0 := context_zero k 3 [17] []
lemma extend_176_22 : a k 22*normalRep k ⟨(18,15),by decide⟩=0 := by
  change a k 22*wordValue (a k) [17, 12] = 0
  rw [show a k 22*wordValue (a k) [17, 12]=wordValue (a k) [17, 12, 22] from (word_snoc (a k) [17, 12] 22).symm]
  calc
    wordValue (a k) [17, 12, 22] = 0 := context_zero k 4 [17] []
lemma extend_177_20 : a k 20*normalRep k ⟨(18,16),by decide⟩=normalRep k ⟨(8,16),by decide⟩ := by
  change a k 20*wordValue (a k) [18, 6, 10, 3] = wordValue (a k) [18, 6, 10, 3, 20]
  rw [show a k 20*wordValue (a k) [18, 6, 10, 3]=wordValue (a k) [18, 6, 10, 3, 20] from (word_snoc (a k) [18, 6, 10, 3] 20).symm]
  all_goals rfl
lemma extend_177_21 : a k 21*normalRep k ⟨(18,16),by decide⟩=0 := by
  change a k 21*wordValue (a k) [18, 6, 10, 3] = 0
  rw [show a k 21*wordValue (a k) [18, 6, 10, 3]=wordValue (a k) [18, 6, 10, 3, 21] from (word_snoc (a k) [18, 6, 10, 3] 21).symm]
  calc
    wordValue (a k) [18, 6, 10, 3, 21] = 0 := context_zero k 0 [18, 6, 10] []
lemma extend_177_22 : a k 22*normalRep k ⟨(18,16),by decide⟩=0 := by
  change a k 22*wordValue (a k) [18, 6, 10, 3] = 0
  rw [show a k 22*wordValue (a k) [18, 6, 10, 3]=wordValue (a k) [18, 6, 10, 3, 22] from (word_snoc (a k) [18, 6, 10, 3] 22).symm]
  calc
    wordValue (a k) [18, 6, 10, 3, 22] = 0 := context_zero k 1 [18, 6, 10] []
lemma extend_178_20 : a k 20*normalRep k ⟨(18,17),by decide⟩=normalRep k ⟨(8,17),by decide⟩ := by
  change a k 20*wordValue (a k) [21, 9, 18, 6, 10, 3] = wordValue (a k) [21, 9, 18, 6, 10, 3, 20]
  rw [show a k 20*wordValue (a k) [21, 9, 18, 6, 10, 3]=wordValue (a k) [21, 9, 18, 6, 10, 3, 20] from (word_snoc (a k) [21, 9, 18, 6, 10, 3] 20).symm]
  all_goals rfl
lemma extend_178_21 : a k 21*normalRep k ⟨(18,17),by decide⟩=0 := by
  change a k 21*wordValue (a k) [21, 9, 18, 6, 10, 3] = 0
  rw [show a k 21*wordValue (a k) [21, 9, 18, 6, 10, 3]=wordValue (a k) [21, 9, 18, 6, 10, 3, 21] from (word_snoc (a k) [21, 9, 18, 6, 10, 3] 21).symm]
  calc
    wordValue (a k) [21, 9, 18, 6, 10, 3, 21] = 0 := context_zero k 0 [21, 9, 18, 6, 10] []
lemma extend_178_22 : a k 22*normalRep k ⟨(18,17),by decide⟩=0 := by
  change a k 22*wordValue (a k) [21, 9, 18, 6, 10, 3] = 0
  rw [show a k 22*wordValue (a k) [21, 9, 18, 6, 10, 3]=wordValue (a k) [21, 9, 18, 6, 10, 3, 22] from (word_snoc (a k) [21, 9, 18, 6, 10, 3] 22).symm]
  calc
    wordValue (a k) [21, 9, 18, 6, 10, 3, 22] = 0 := context_zero k 1 [21, 9, 18, 6, 10] []

def lastArrow (i j : Fin 19) : Fin 23 := (normalWord i j).getLastD 0
theorem lastArrow_spec : ∀ i j, Allowed i j → i≠j →
    normalWord i j=(normalWord i j).dropLast++[lastArrow i j] ∧ arrowTarget (lastArrow i j)=slotVertex i := by decide
lemma vertex_word (v : Fin 18) (p : List (Fin 23)) (b : Fin 23) :
    e k v*wordValue (a k) (p++[b]) = if v=arrowTarget b then wordValue (a k) (p++[b]) else 0 := by
  rw [word_append]
  simp only [wordValue,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  rw [← mul_assoc,va]
  split_ifs <;> simp
lemma incompatible_pair (b d : Fin 23) (h : arrowTarget d≠arrowSource b) : a k b*a k d=0 := by
  have hv : e k (arrowTarget d)*a k d=a k d := by rw [va,if_pos rfl]
  rw [← hv,← mul_assoc,av,if_neg h,zero_mul]
lemma incompatible_word (b d : Fin 23) (p : List (Fin 23)) (h : arrowTarget d≠arrowSource b) :
    a k b*wordValue (a k) (p++[d])=0 := by
  rw [word_append]
  simp only [wordValue,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  rw [← mul_assoc,incompatible_pair k b d h,zero_mul]
lemma vertex_normalRep (v : Fin 18) (c : Coord) :
    e k v*normalRep k c=if v=slotVertex c.val.1 then normalRep k c else 0 := by
  by_cases h : c.val.1=c.val.2
  · simp only [normalRep,if_pos h,vv]
    split_ifs <;> simp_all
  · have hs := lastArrow_spec c.val.1 c.val.2 c.property.1 h
    simp only [normalRep,if_neg h]
    rw [hs.1,vertex_word,hs.2]
lemma incompatible_normalRep (b : Fin 23) (c : Coord) (h : arrowSource b≠slotVertex c.val.1) :
    a k b*normalRep k c=0 := by
  by_cases he : c.val.1=c.val.2
  · simp only [normalRep,if_pos he,av,if_neg (Ne.symm h)]
  · have hs := lastArrow_spec c.val.1 c.val.2 c.property.1 he
    simp only [normalRep,if_neg he]
    rw [hs.1]
    apply incompatible_word
    simpa [hs.2] using Ne.symm h

def normalSpan : Submodule k (Presented k) := Submodule.span k (Set.range (normalRep k))
lemma normal_mem (c : Coord) : normalRep k c ∈ normalSpan k := Submodule.subset_span ⟨c,rfl⟩
lemma vertex_span (v : Fin 18) (c : Coord) : e k v*normalRep k c ∈ normalSpan k := by
  rw [vertex_normalRep]
  split_ifs
  · exact normal_mem k c
  · exact Submodule.zero_mem _
lemma arrow_span (b : Fin 23) (c : Coord) : a k b*normalRep k c ∈ normalSpan k := by
  by_cases h : arrowSource b=slotVertex c.val.1
  · rcases c with ⟨⟨i,j⟩,hc⟩
    fin_cases i
    · fin_cases j
      · fin_cases b
        · change a k 0*normalRep k ⟨(0,0),by decide⟩ ∈ normalSpan k
          rw [extend_0_0 k]
          exact normal_mem k ⟨(1,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 0)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 0)) h)
      · exact False.elim ((by decide : ¬(Allowed 0 1 ∧ ((0,1) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 2 ∧ ((0,2) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 3 ∧ ((0,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 4 ∧ ((0,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 5 ∧ ((0,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 6 ∧ ((0,6) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 7 ∧ ((0,7) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 8 ∧ ((0,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 9 ∧ ((0,9) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 10 ∧ ((0,10) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 11 ∧ ((0,11) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 12 ∧ ((0,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 13 ∧ ((0,13) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 14 ∧ ((0,14) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 15 ∧ ((0,15) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 16 ∧ ((0,16) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 17 ∧ ((0,17) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 0 18 ∧ ((0,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 1)) h)
        · change a k 1*normalRep k ⟨(1,0),by decide⟩ ∈ normalSpan k
          rw [extend_1_1 k]
          exact normal_mem k ⟨(6,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 1)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 1)) h)
        · change a k 1*normalRep k ⟨(1,1),by decide⟩ ∈ normalSpan k
          rw [extend_2_1 k]
          exact normal_mem k ⟨(6,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 1)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 1)) h)
      · exact False.elim ((by decide : ¬(Allowed 1 2 ∧ ((1,2) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 3 ∧ ((1,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 4 ∧ ((1,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 5 ∧ ((1,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 6 ∧ ((1,6) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 7 ∧ ((1,7) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 8 ∧ ((1,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 9 ∧ ((1,9) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 10 ∧ ((1,10) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 11 ∧ ((1,11) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 12 ∧ ((1,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 13 ∧ ((1,13) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 14 ∧ ((1,14) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 15 ∧ ((1,15) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 16 ∧ ((1,16) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 17 ∧ ((1,17) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 1 18 ∧ ((1,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 2)) h)
        · change a k 2*normalRep k ⟨(2,0),by decide⟩ ∈ normalSpan k
          rw [extend_3_2 k]
          exact normal_mem k ⟨(7,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 2)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 2)) h)
        · change a k 2*normalRep k ⟨(2,1),by decide⟩ ∈ normalSpan k
          rw [extend_4_2 k]
          exact normal_mem k ⟨(7,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 2)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 2)) h)
        · change a k 2*normalRep k ⟨(2,2),by decide⟩ ∈ normalSpan k
          rw [extend_5_2 k]
          exact normal_mem k ⟨(7,2),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 2)) h)
      · exact False.elim ((by decide : ¬(Allowed 2 3 ∧ ((2,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 2 4 ∧ ((2,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 2 5 ∧ ((2,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 2)) h)
        · change a k 2*normalRep k ⟨(2,6),by decide⟩ ∈ normalSpan k
          rw [extend_6_2 k]
          exact normal_mem k ⟨(7,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 2)) h)
      · exact False.elim ((by decide : ¬(Allowed 2 7 ∧ ((2,7) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 2 8 ∧ ((2,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 2)) h)
        · change a k 2*normalRep k ⟨(2,9),by decide⟩ ∈ normalSpan k
          rw [extend_7_2 k]
          exact normal_mem k ⟨(7,9),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 2)) h)
      · exact False.elim ((by decide : ¬(Allowed 2 10 ∧ ((2,10) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 2 11 ∧ ((2,11) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 2 12 ∧ ((2,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 2)) h)
        · change a k 2*normalRep k ⟨(2,13),by decide⟩ ∈ normalSpan k
          rw [extend_8_2 k]
          exact normal_mem k ⟨(7,13),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 2)) h)
      · exact False.elim ((by decide : ¬(Allowed 2 14 ∧ ((2,14) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 2 15 ∧ ((2,15) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 2 16 ∧ ((2,16) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 2)) h)
        · change a k 2*normalRep k ⟨(2,17),by decide⟩ ∈ normalSpan k
          rw [extend_9_2 k]
          exact normal_mem k ⟨(7,17),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 2)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 2)) h)
      · exact False.elim ((by decide : ¬(Allowed 2 18 ∧ ((2,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 3)) h)
        · change a k 3*normalRep k ⟨(3,0),by decide⟩ ∈ normalSpan k
          rw [extend_10_3 k]
          exact normal_mem k ⟨(18,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 3)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 3)) h)
        · change a k 3*normalRep k ⟨(3,1),by decide⟩ ∈ normalSpan k
          rw [extend_11_3 k]
          exact normal_mem k ⟨(18,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 3)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 3)) h)
        · change a k 3*normalRep k ⟨(3,2),by decide⟩ ∈ normalSpan k
          rw [extend_12_3 k]
          exact normal_mem k ⟨(18,2),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 3)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 3)) h)
        · change a k 3*normalRep k ⟨(3,3),by decide⟩ ∈ normalSpan k
          rw [extend_13_3 k]
          exact normal_mem k ⟨(18,3),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 3)) h)
      · exact False.elim ((by decide : ¬(Allowed 3 4 ∧ ((3,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 3 5 ∧ ((3,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 3)) h)
        · change a k 3*normalRep k ⟨(3,6),by decide⟩ ∈ normalSpan k
          rw [extend_14_3 k]
          exact normal_mem k ⟨(18,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 3)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 3)) h)
        · change a k 3*normalRep k ⟨(3,7),by decide⟩ ∈ normalSpan k
          rw [extend_15_3 k]
          exact normal_mem k ⟨(18,7),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 3)) h)
      · exact False.elim ((by decide : ¬(Allowed 3 8 ∧ ((3,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 3)) h)
        · change a k 3*normalRep k ⟨(3,9),by decide⟩ ∈ normalSpan k
          rw [extend_16_3 k]
          exact normal_mem k ⟨(18,9),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 3)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 3)) h)
        · change a k 3*normalRep k ⟨(3,10),by decide⟩ ∈ normalSpan k
          rw [extend_17_3 k]
          exact normal_mem k ⟨(18,10),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 3)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 3)) h)
        · change a k 3*normalRep k ⟨(3,11),by decide⟩ ∈ normalSpan k
          rw [extend_18_3 k]
          exact normal_mem k ⟨(18,11),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 3)) h)
      · exact False.elim ((by decide : ¬(Allowed 3 12 ∧ ((3,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 3)) h)
        · change a k 3*normalRep k ⟨(3,13),by decide⟩ ∈ normalSpan k
          rw [extend_19_3 k]
          exact normal_mem k ⟨(18,13),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 3)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 3)) h)
        · change a k 3*normalRep k ⟨(3,14),by decide⟩ ∈ normalSpan k
          rw [extend_20_3 k]
          exact normal_mem k ⟨(18,14),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 3)) h)
      · exact False.elim ((by decide : ¬(Allowed 3 15 ∧ ((3,15) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 3)) h)
        · change a k 3*normalRep k ⟨(3,16),by decide⟩ ∈ normalSpan k
          rw [extend_21_3 k]
          exact normal_mem k ⟨(18,16),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 3)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 3)) h)
        · change a k 3*normalRep k ⟨(3,17),by decide⟩ ∈ normalSpan k
          rw [extend_22_3 k]
          exact normal_mem k ⟨(18,17),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 3)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 3)) h)
      · exact False.elim ((by decide : ¬(Allowed 3 18 ∧ ((3,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,0),by decide⟩ ∈ normalSpan k
          rw [extend_23_4 k]
          exact normal_mem k ⟨(5,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,1),by decide⟩ ∈ normalSpan k
          rw [extend_24_4 k]
          exact normal_mem k ⟨(5,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,2),by decide⟩ ∈ normalSpan k
          rw [extend_25_4 k]
          exact normal_mem k ⟨(5,2),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,3),by decide⟩ ∈ normalSpan k
          rw [extend_26_4 k]
          exact normal_mem k ⟨(5,3),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,4),by decide⟩ ∈ normalSpan k
          rw [extend_27_4 k]
          exact normal_mem k ⟨(5,4),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · exact False.elim ((by decide : ¬(Allowed 4 5 ∧ ((4,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,6),by decide⟩ ∈ normalSpan k
          rw [extend_28_4 k]
          exact normal_mem k ⟨(5,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,7),by decide⟩ ∈ normalSpan k
          rw [extend_29_4 k]
          exact normal_mem k ⟨(5,7),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,8),by decide⟩ ∈ normalSpan k
          rw [extend_30_4 k]
          exact normal_mem k ⟨(5,8),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,9),by decide⟩ ∈ normalSpan k
          rw [extend_31_4 k]
          exact normal_mem k ⟨(5,9),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,10),by decide⟩ ∈ normalSpan k
          rw [extend_32_4 k]
          exact normal_mem k ⟨(5,10),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,11),by decide⟩ ∈ normalSpan k
          rw [extend_33_4 k]
          exact normal_mem k ⟨(5,11),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,12),by decide⟩ ∈ normalSpan k
          rw [extend_34_4 k]
          exact normal_mem k ⟨(5,12),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,13),by decide⟩ ∈ normalSpan k
          rw [extend_35_4 k]
          exact normal_mem k ⟨(5,13),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,14),by decide⟩ ∈ normalSpan k
          rw [extend_36_4 k]
          exact normal_mem k ⟨(5,14),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,15),by decide⟩ ∈ normalSpan k
          rw [extend_37_4 k]
          exact normal_mem k ⟨(5,15),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,16),by decide⟩ ∈ normalSpan k
          rw [extend_38_4 k]
          exact normal_mem k ⟨(5,16),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,17),by decide⟩ ∈ normalSpan k
          rw [extend_39_4 k]
          exact normal_mem k ⟨(5,17),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 4)) h)
        · change a k 4*normalRep k ⟨(4,18),by decide⟩ ∈ normalSpan k
          rw [extend_40_4 k]
          exact normal_mem k ⟨(5,18),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 4)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 4)) h)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 5)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 5)) h)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 6)) h)
        · change a k 5*normalRep k ⟨(6,0),by decide⟩ ∈ normalSpan k
          rw [extend_60_5 k]
          exact normal_mem k ⟨(9,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 6)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 6)) h)
        · change a k 5*normalRep k ⟨(6,1),by decide⟩ ∈ normalSpan k
          rw [extend_61_5 k]
          exact normal_mem k ⟨(9,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 6)) h)
      · exact False.elim ((by decide : ¬(Allowed 6 2 ∧ ((6,2) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 3 ∧ ((6,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 4 ∧ ((6,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 5 ∧ ((6,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 6)) h)
        · change a k 5*normalRep k ⟨(6,6),by decide⟩ ∈ normalSpan k
          rw [extend_62_5 k]
          exact normal_mem k ⟨(9,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 6)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 6)) h)
      · exact False.elim ((by decide : ¬(Allowed 6 7 ∧ ((6,7) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 8 ∧ ((6,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 9 ∧ ((6,9) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 10 ∧ ((6,10) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 11 ∧ ((6,11) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 12 ∧ ((6,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 13 ∧ ((6,13) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 14 ∧ ((6,14) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 15 ∧ ((6,15) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 16 ∧ ((6,16) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 17 ∧ ((6,17) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 6 18 ∧ ((6,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 7)) h)
        · change a k 6*normalRep k ⟨(7,0),by decide⟩ ∈ normalSpan k
          rw [extend_63_6 k]
          exact normal_mem k ⟨(11,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 7)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 7)) h)
        · change a k 6*normalRep k ⟨(7,1),by decide⟩ ∈ normalSpan k
          rw [extend_64_6 k]
          exact normal_mem k ⟨(11,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 7)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 7)) h)
        · change a k 6*normalRep k ⟨(7,2),by decide⟩ ∈ normalSpan k
          rw [extend_65_6 k]
          exact normal_mem k ⟨(11,2),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 7)) h)
      · exact False.elim ((by decide : ¬(Allowed 7 3 ∧ ((7,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 7 4 ∧ ((7,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 7 5 ∧ ((7,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 7)) h)
        · change a k 6*normalRep k ⟨(7,6),by decide⟩ ∈ normalSpan k
          rw [extend_66_6 k]
          exact normal_mem k ⟨(11,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 7)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 7)) h)
        · change a k 6*normalRep k ⟨(7,7),by decide⟩ ∈ normalSpan k
          rw [extend_67_6 k]
          exact normal_mem k ⟨(11,7),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 7)) h)
      · exact False.elim ((by decide : ¬(Allowed 7 8 ∧ ((7,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 7)) h)
        · change a k 6*normalRep k ⟨(7,9),by decide⟩ ∈ normalSpan k
          rw [extend_68_6 k]
          exact normal_mem k ⟨(11,9),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 7)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 7)) h)
        · change a k 6*normalRep k ⟨(7,10),by decide⟩ ∈ normalSpan k
          rw [extend_69_6 k]
          exact normal_mem k ⟨(11,10),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 7)) h)
      · exact False.elim ((by decide : ¬(Allowed 7 11 ∧ ((7,11) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 7 12 ∧ ((7,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 7)) h)
        · change a k 6*normalRep k ⟨(7,13),by decide⟩ ∈ normalSpan k
          rw [extend_70_6 k]
          exact normal_mem k ⟨(11,13),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 7)) h)
      · exact False.elim ((by decide : ¬(Allowed 7 14 ∧ ((7,14) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 7 15 ∧ ((7,15) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 7)) h)
        · change a k 6*normalRep k ⟨(7,16),by decide⟩ ∈ normalSpan k
          rw [extend_71_6 k]
          exact normal_mem k ⟨(11,16),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 7)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 7)) h)
        · change a k 6*normalRep k ⟨(7,17),by decide⟩ ∈ normalSpan k
          rw [extend_72_6 k]
          exact normal_mem k ⟨(11,17),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 7)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 7)) h)
      · exact False.elim ((by decide : ¬(Allowed 7 18 ∧ ((7,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,0),by decide⟩ ∈ normalSpan k
          rw [extend_73_7 k]
          exact normal_mem k ⟨(4,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,1),by decide⟩ ∈ normalSpan k
          rw [extend_74_7 k]
          exact normal_mem k ⟨(4,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,2),by decide⟩ ∈ normalSpan k
          rw [extend_75_7 k]
          exact normal_mem k ⟨(4,2),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,3),by decide⟩ ∈ normalSpan k
          rw [extend_76_7 k]
          exact normal_mem k ⟨(4,3),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · exact False.elim ((by decide : ¬(Allowed 8 4 ∧ ((8,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 8 5 ∧ ((8,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,6),by decide⟩ ∈ normalSpan k
          rw [extend_77_7 k]
          exact normal_mem k ⟨(4,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,7),by decide⟩ ∈ normalSpan k
          rw [extend_78_7 k]
          exact normal_mem k ⟨(4,7),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,8),by decide⟩ ∈ normalSpan k
          rw [extend_79_7 k]
          exact normal_mem k ⟨(4,8),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,9),by decide⟩ ∈ normalSpan k
          rw [extend_80_7 k]
          exact normal_mem k ⟨(4,9),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,10),by decide⟩ ∈ normalSpan k
          rw [extend_81_7 k]
          exact normal_mem k ⟨(4,10),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,11),by decide⟩ ∈ normalSpan k
          rw [extend_82_7 k]
          exact normal_mem k ⟨(4,11),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,12),by decide⟩ ∈ normalSpan k
          rw [extend_83_7 k]
          exact normal_mem k ⟨(4,12),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,13),by decide⟩ ∈ normalSpan k
          rw [extend_84_7 k]
          exact normal_mem k ⟨(4,13),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,14),by decide⟩ ∈ normalSpan k
          rw [extend_85_7 k]
          exact normal_mem k ⟨(4,14),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,15),by decide⟩ ∈ normalSpan k
          rw [extend_86_7 k]
          exact normal_mem k ⟨(4,15),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,16),by decide⟩ ∈ normalSpan k
          rw [extend_87_7 k]
          exact normal_mem k ⟨(4,16),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,17),by decide⟩ ∈ normalSpan k
          rw [extend_88_7 k]
          exact normal_mem k ⟨(4,17),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 8)) h)
        · change a k 7*normalRep k ⟨(8,18),by decide⟩ ∈ normalSpan k
          rw [extend_89_7 k]
          exact normal_mem k ⟨(4,18),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 8)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 8)) h)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 9)) h)
        · change a k 8*normalRep k ⟨(9,0),by decide⟩ ∈ normalSpan k
          rw [extend_90_8 k]
          exact normal_mem k ⟨(17,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 9)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 9)) h)
        · change a k 8*normalRep k ⟨(9,1),by decide⟩ ∈ normalSpan k
          rw [extend_91_8 k]
          exact normal_mem k ⟨(17,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 9)) h)
      · exact False.elim ((by decide : ¬(Allowed 9 2 ∧ ((9,2) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 9 3 ∧ ((9,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 9 4 ∧ ((9,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 9 5 ∧ ((9,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 9)) h)
        · change a k 8*normalRep k ⟨(9,6),by decide⟩ ∈ normalSpan k
          rw [extend_92_8 k]
          exact normal_mem k ⟨(17,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 9)) h)
      · exact False.elim ((by decide : ¬(Allowed 9 7 ∧ ((9,7) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 9 8 ∧ ((9,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 9)) h)
        · change a k 8*normalRep k ⟨(9,9),by decide⟩ ∈ normalSpan k
          rw [extend_93_8 k]
          exact normal_mem k ⟨(17,9),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 9)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 9)) h)
      · exact False.elim ((by decide : ¬(Allowed 9 10 ∧ ((9,10) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 9 11 ∧ ((9,11) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 9 12 ∧ ((9,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 9 13 ∧ ((9,13) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 9 14 ∧ ((9,14) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 9 15 ∧ ((9,15) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 9 16 ∧ ((9,16) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 9 17 ∧ ((9,17) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 9 18 ∧ ((9,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 10)) h)
        · change a k 9*normalRep k ⟨(10,0),by decide⟩ ∈ normalSpan k
          rw [extend_94_9 k]
          exact normal_mem k ⟨(16,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 10)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 10)) h)
        · change a k 9*normalRep k ⟨(10,1),by decide⟩ ∈ normalSpan k
          rw [extend_95_9 k]
          exact normal_mem k ⟨(16,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 10)) h)
      · exact False.elim ((by decide : ¬(Allowed 10 2 ∧ ((10,2) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 10 3 ∧ ((10,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 10 4 ∧ ((10,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 10 5 ∧ ((10,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 10)) h)
        · change a k 9*normalRep k ⟨(10,6),by decide⟩ ∈ normalSpan k
          rw [extend_96_9 k]
          exact normal_mem k ⟨(16,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 10)) h)
      · exact False.elim ((by decide : ¬(Allowed 10 7 ∧ ((10,7) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 10 8 ∧ ((10,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 10)) h)
        · change a k 9*normalRep k ⟨(10,9),by decide⟩ ∈ normalSpan k
          rw [extend_97_9 k]
          exact normal_mem k ⟨(16,9),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 10)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 10)) h)
        · change a k 9*normalRep k ⟨(10,10),by decide⟩ ∈ normalSpan k
          rw [extend_98_9 k]
          exact normal_mem k ⟨(16,10),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 10)) h)
      · exact False.elim ((by decide : ¬(Allowed 10 11 ∧ ((10,11) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 10 12 ∧ ((10,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 10 13 ∧ ((10,13) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 10 14 ∧ ((10,14) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 10 15 ∧ ((10,15) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 10 16 ∧ ((10,16) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 10)) h)
        · change a k 9*normalRep k ⟨(10,17),by decide⟩ ∈ normalSpan k
          rw [extend_99_9 k]
          exact normal_mem k ⟨(16,17),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 10)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 10)) h)
      · exact False.elim ((by decide : ¬(Allowed 10 18 ∧ ((10,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 11)) h)
        · change a k 10*normalRep k ⟨(11,0),by decide⟩ ∈ normalSpan k
          rw [extend_100_10 k]
          exact normal_mem k ⟨(3,0),by decide⟩
        · change a k 11*normalRep k ⟨(11,0),by decide⟩ ∈ normalSpan k
          rw [extend_100_11 k]
          exact normal_mem k ⟨(12,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 11)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 11)) h)
        · change a k 10*normalRep k ⟨(11,1),by decide⟩ ∈ normalSpan k
          rw [extend_101_10 k]
          exact normal_mem k ⟨(3,1),by decide⟩
        · change a k 11*normalRep k ⟨(11,1),by decide⟩ ∈ normalSpan k
          rw [extend_101_11 k]
          exact normal_mem k ⟨(12,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 11)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 11)) h)
        · change a k 10*normalRep k ⟨(11,2),by decide⟩ ∈ normalSpan k
          rw [extend_102_10 k]
          exact normal_mem k ⟨(3,2),by decide⟩
        · change a k 11*normalRep k ⟨(11,2),by decide⟩ ∈ normalSpan k
          rw [extend_102_11 k]
          exact normal_mem k ⟨(12,2),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 11)) h)
      · exact False.elim ((by decide : ¬(Allowed 11 3 ∧ ((11,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 11 4 ∧ ((11,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 11 5 ∧ ((11,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 11)) h)
        · change a k 10*normalRep k ⟨(11,6),by decide⟩ ∈ normalSpan k
          rw [extend_103_10 k]
          exact normal_mem k ⟨(3,6),by decide⟩
        · change a k 11*normalRep k ⟨(11,6),by decide⟩ ∈ normalSpan k
          rw [extend_103_11 k]
          exact normal_mem k ⟨(12,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 11)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 11)) h)
        · change a k 10*normalRep k ⟨(11,7),by decide⟩ ∈ normalSpan k
          rw [extend_104_10 k]
          exact normal_mem k ⟨(3,7),by decide⟩
        · change a k 11*normalRep k ⟨(11,7),by decide⟩ ∈ normalSpan k
          rw [extend_104_11 k]
          exact normal_mem k ⟨(12,7),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 11)) h)
      · exact False.elim ((by decide : ¬(Allowed 11 8 ∧ ((11,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 11)) h)
        · change a k 10*normalRep k ⟨(11,9),by decide⟩ ∈ normalSpan k
          rw [extend_105_10 k]
          exact normal_mem k ⟨(3,9),by decide⟩
        · change a k 11*normalRep k ⟨(11,9),by decide⟩ ∈ normalSpan k
          rw [extend_105_11 k]
          exact normal_mem k ⟨(12,9),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 11)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 11)) h)
        · change a k 10*normalRep k ⟨(11,10),by decide⟩ ∈ normalSpan k
          rw [extend_106_10 k]
          exact normal_mem k ⟨(3,10),by decide⟩
        · change a k 11*normalRep k ⟨(11,10),by decide⟩ ∈ normalSpan k
          rw [extend_106_11 k]
          exact normal_mem k ⟨(12,10),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 11)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 11)) h)
        · change a k 10*normalRep k ⟨(11,11),by decide⟩ ∈ normalSpan k
          rw [extend_107_10 k]
          exact normal_mem k ⟨(3,11),by decide⟩
        · change a k 11*normalRep k ⟨(11,11),by decide⟩ ∈ normalSpan k
          rw [extend_107_11 k]
          exact normal_mem k ⟨(12,11),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 11)) h)
      · exact False.elim ((by decide : ¬(Allowed 11 12 ∧ ((11,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 11)) h)
        · change a k 10*normalRep k ⟨(11,13),by decide⟩ ∈ normalSpan k
          rw [extend_108_10 k]
          exact normal_mem k ⟨(3,13),by decide⟩
        · change a k 11*normalRep k ⟨(11,13),by decide⟩ ∈ normalSpan k
          rw [extend_108_11 k]
          exact normal_mem k ⟨(12,13),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 11)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 11)) h)
        · change a k 10*normalRep k ⟨(11,14),by decide⟩ ∈ normalSpan k
          rw [extend_109_10 k]
          exact normal_mem k ⟨(3,14),by decide⟩
        · change a k 11*normalRep k ⟨(11,14),by decide⟩ ∈ normalSpan k
          rw [extend_109_11 k]
          exact normal_mem k ⟨(12,14),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 11)) h)
      · exact False.elim ((by decide : ¬(Allowed 11 15 ∧ ((11,15) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 11)) h)
        · change a k 10*normalRep k ⟨(11,16),by decide⟩ ∈ normalSpan k
          rw [extend_110_10 k]
          exact normal_mem k ⟨(3,16),by decide⟩
        · change a k 11*normalRep k ⟨(11,16),by decide⟩ ∈ normalSpan k
          rw [extend_110_11 k]
          exact normal_mem k ⟨(12,16),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 11)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 11)) h)
        · change a k 10*normalRep k ⟨(11,17),by decide⟩ ∈ normalSpan k
          rw [extend_111_10 k]
          exact normal_mem k ⟨(3,17),by decide⟩
        · change a k 11*normalRep k ⟨(11,17),by decide⟩ ∈ normalSpan k
          rw [extend_111_11 k]
          exact normal_mem k ⟨(12,17),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 11)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 11)) h)
      · exact False.elim ((by decide : ¬(Allowed 11 18 ∧ ((11,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,0),by decide⟩ ∈ normalSpan k
          rw [extend_112_12 k]
          exact normal_mem k ⟨(18,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,1),by decide⟩ ∈ normalSpan k
          rw [extend_113_12 k]
          exact normal_mem k ⟨(18,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,2),by decide⟩ ∈ normalSpan k
          rw [extend_114_12 k]
          exact normal_mem k ⟨(18,2),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · exact False.elim ((by decide : ¬(Allowed 12 3 ∧ ((12,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 12 4 ∧ ((12,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 12 5 ∧ ((12,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,6),by decide⟩ ∈ normalSpan k
          rw [extend_115_12 k]
          exact normal_mem k ⟨(18,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,7),by decide⟩ ∈ normalSpan k
          rw [extend_116_12 k]
          exact normal_mem k ⟨(18,7),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · exact False.elim ((by decide : ¬(Allowed 12 8 ∧ ((12,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,9),by decide⟩ ∈ normalSpan k
          rw [extend_117_12 k]
          exact normal_mem k ⟨(18,9),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,10),by decide⟩ ∈ normalSpan k
          rw [extend_118_12 k]
          exact normal_mem k ⟨(18,10),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,11),by decide⟩ ∈ normalSpan k
          rw [extend_119_12 k]
          exact normal_mem k ⟨(18,11),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,12),by decide⟩ ∈ normalSpan k
          rw [extend_120_12 k]
          exact normal_mem k ⟨(18,12),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,13),by decide⟩ ∈ normalSpan k
          rw [extend_121_12 k]
          exact normal_mem k ⟨(18,13),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,14),by decide⟩ ∈ normalSpan k
          rw [extend_122_12 k]
          exact normal_mem k ⟨(18,14),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,15),by decide⟩ ∈ normalSpan k
          rw [extend_123_12 k]
          exact normal_mem k ⟨(18,15),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,16),by decide⟩ ∈ normalSpan k
          rw [extend_124_12 k]
          exact normal_mem k ⟨(18,16),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 12)) h)
        · change a k 12*normalRep k ⟨(12,17),by decide⟩ ∈ normalSpan k
          rw [extend_125_12 k]
          exact normal_mem k ⟨(18,17),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 12)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 12)) h)
      · exact False.elim ((by decide : ¬(Allowed 12 18 ∧ ((12,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 13)) h)
        · change a k 13*normalRep k ⟨(13,0),by decide⟩ ∈ normalSpan k
          rw [extend_126_13 k]
          exact normal_mem k ⟨(2,0),by decide⟩
        · change a k 14*normalRep k ⟨(13,0),by decide⟩ ∈ normalSpan k
          rw [extend_126_14 k]
          exact normal_mem k ⟨(16,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 13)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 13)) h)
        · change a k 13*normalRep k ⟨(13,1),by decide⟩ ∈ normalSpan k
          rw [extend_127_13 k]
          exact normal_mem k ⟨(2,1),by decide⟩
        · change a k 14*normalRep k ⟨(13,1),by decide⟩ ∈ normalSpan k
          rw [extend_127_14 k]
          exact normal_mem k ⟨(16,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 13)) h)
      · exact False.elim ((by decide : ¬(Allowed 13 2 ∧ ((13,2) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 13 3 ∧ ((13,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 13 4 ∧ ((13,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 13 5 ∧ ((13,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 13)) h)
        · change a k 13*normalRep k ⟨(13,6),by decide⟩ ∈ normalSpan k
          rw [extend_128_13 k]
          exact normal_mem k ⟨(2,6),by decide⟩
        · change a k 14*normalRep k ⟨(13,6),by decide⟩ ∈ normalSpan k
          rw [extend_128_14 k]
          exact normal_mem k ⟨(16,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 13)) h)
      · exact False.elim ((by decide : ¬(Allowed 13 7 ∧ ((13,7) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 13 8 ∧ ((13,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 13)) h)
        · change a k 13*normalRep k ⟨(13,9),by decide⟩ ∈ normalSpan k
          rw [extend_129_13 k]
          exact normal_mem k ⟨(2,9),by decide⟩
        · change a k 14*normalRep k ⟨(13,9),by decide⟩ ∈ normalSpan k
          rw [extend_129_14 k]
          exact normal_mem k ⟨(16,9),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 13)) h)
      · exact False.elim ((by decide : ¬(Allowed 13 10 ∧ ((13,10) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 13 11 ∧ ((13,11) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 13 12 ∧ ((13,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 13)) h)
        · change a k 13*normalRep k ⟨(13,13),by decide⟩ ∈ normalSpan k
          rw [extend_130_13 k]
          exact normal_mem k ⟨(2,13),by decide⟩
        · change a k 14*normalRep k ⟨(13,13),by decide⟩ ∈ normalSpan k
          rw [extend_130_14 k]
          exact normal_mem k ⟨(16,13),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 13)) h)
      · exact False.elim ((by decide : ¬(Allowed 13 14 ∧ ((13,14) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 13 15 ∧ ((13,15) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 13 16 ∧ ((13,16) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 13)) h)
        · change a k 13*normalRep k ⟨(13,17),by decide⟩ ∈ normalSpan k
          rw [extend_131_13 k]
          exact normal_mem k ⟨(2,17),by decide⟩
        · change a k 14*normalRep k ⟨(13,17),by decide⟩ ∈ normalSpan k
          rw [extend_131_14 k]
          exact normal_mem k ⟨(16,17),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 13)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 13)) h)
      · exact False.elim ((by decide : ¬(Allowed 13 18 ∧ ((13,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 14)) h)
        · change a k 15*normalRep k ⟨(14,0),by decide⟩ ∈ normalSpan k
          rw [extend_132_15 k]
          exact normal_mem k ⟨(11,0),by decide⟩
        · change a k 16*normalRep k ⟨(14,0),by decide⟩ ∈ normalSpan k
          rw [extend_132_16 k]
          exact normal_mem k ⟨(15,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 14)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 14)) h)
        · change a k 15*normalRep k ⟨(14,1),by decide⟩ ∈ normalSpan k
          rw [extend_133_15 k]
          exact normal_mem k ⟨(11,1),by decide⟩
        · change a k 16*normalRep k ⟨(14,1),by decide⟩ ∈ normalSpan k
          rw [extend_133_16 k]
          exact normal_mem k ⟨(15,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 14)) h)
      · exact False.elim ((by decide : ¬(Allowed 14 2 ∧ ((14,2) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 14 3 ∧ ((14,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 14 4 ∧ ((14,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 14 5 ∧ ((14,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 14)) h)
        · change a k 15*normalRep k ⟨(14,6),by decide⟩ ∈ normalSpan k
          rw [extend_134_15 k]
          exact normal_mem k ⟨(11,6),by decide⟩
        · change a k 16*normalRep k ⟨(14,6),by decide⟩ ∈ normalSpan k
          rw [extend_134_16 k]
          exact normal_mem k ⟨(15,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 14)) h)
      · exact False.elim ((by decide : ¬(Allowed 14 7 ∧ ((14,7) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 14 8 ∧ ((14,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 14)) h)
        · change a k 15*normalRep k ⟨(14,9),by decide⟩ ∈ normalSpan k
          rw [extend_135_15 k]
          exact normal_mem k ⟨(11,9),by decide⟩
        · change a k 16*normalRep k ⟨(14,9),by decide⟩ ∈ normalSpan k
          rw [extend_135_16 k]
          exact normal_mem k ⟨(15,9),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 14)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 14)) h)
        · change a k 15*normalRep k ⟨(14,10),by decide⟩ ∈ normalSpan k
          rw [extend_136_15 k]
          exact normal_mem k ⟨(11,10),by decide⟩
        · change a k 16*normalRep k ⟨(14,10),by decide⟩ ∈ normalSpan k
          rw [extend_136_16 k]
          exact normal_mem k ⟨(15,10),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 14)) h)
      · exact False.elim ((by decide : ¬(Allowed 14 11 ∧ ((14,11) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 14 12 ∧ ((14,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 14)) h)
        · change a k 15*normalRep k ⟨(14,13),by decide⟩ ∈ normalSpan k
          rw [extend_137_15 k]
          exact normal_mem k ⟨(11,13),by decide⟩
        · change a k 16*normalRep k ⟨(14,13),by decide⟩ ∈ normalSpan k
          rw [extend_137_16 k]
          exact normal_mem k ⟨(15,13),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 14)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 14)) h)
        · change a k 15*normalRep k ⟨(14,14),by decide⟩ ∈ normalSpan k
          rw [extend_138_15 k]
          exact normal_mem k ⟨(11,14),by decide⟩
        · change a k 16*normalRep k ⟨(14,14),by decide⟩ ∈ normalSpan k
          rw [extend_138_16 k]
          exact normal_mem k ⟨(15,14),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 14)) h)
      · exact False.elim ((by decide : ¬(Allowed 14 15 ∧ ((14,15) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 14)) h)
        · change a k 15*normalRep k ⟨(14,16),by decide⟩ ∈ normalSpan k
          rw [extend_139_15 k]
          exact normal_mem k ⟨(11,16),by decide⟩
        · change a k 16*normalRep k ⟨(14,16),by decide⟩ ∈ normalSpan k
          rw [extend_139_16 k]
          exact normal_mem k ⟨(15,16),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 14)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 14)) h)
        · change a k 15*normalRep k ⟨(14,17),by decide⟩ ∈ normalSpan k
          rw [extend_140_15 k]
          exact normal_mem k ⟨(11,17),by decide⟩
        · change a k 16*normalRep k ⟨(14,17),by decide⟩ ∈ normalSpan k
          rw [extend_140_16 k]
          exact normal_mem k ⟨(15,17),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 14)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 14)) h)
      · exact False.elim ((by decide : ¬(Allowed 14 18 ∧ ((14,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 15)) h)
        · change a k 17*normalRep k ⟨(15,0),by decide⟩ ∈ normalSpan k
          rw [extend_141_17 k]
          exact normal_mem k ⟨(12,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 15)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 15)) h)
        · change a k 17*normalRep k ⟨(15,1),by decide⟩ ∈ normalSpan k
          rw [extend_142_17 k]
          exact normal_mem k ⟨(12,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 15)) h)
      · exact False.elim ((by decide : ¬(Allowed 15 2 ∧ ((15,2) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 15 3 ∧ ((15,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 15 4 ∧ ((15,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 15 5 ∧ ((15,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 15)) h)
        · change a k 17*normalRep k ⟨(15,6),by decide⟩ ∈ normalSpan k
          rw [extend_143_17 k]
          exact normal_mem k ⟨(12,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 15)) h)
      · exact False.elim ((by decide : ¬(Allowed 15 7 ∧ ((15,7) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 15 8 ∧ ((15,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 15)) h)
        · change a k 17*normalRep k ⟨(15,9),by decide⟩ ∈ normalSpan k
          rw [extend_144_17 k]
          exact normal_mem k ⟨(12,9),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 15)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 15)) h)
        · change a k 17*normalRep k ⟨(15,10),by decide⟩ ∈ normalSpan k
          rw [extend_145_17 k]
          exact normal_mem k ⟨(12,10),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 15)) h)
      · exact False.elim ((by decide : ¬(Allowed 15 11 ∧ ((15,11) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 15 12 ∧ ((15,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 15)) h)
        · change a k 17*normalRep k ⟨(15,13),by decide⟩ ∈ normalSpan k
          rw [extend_146_17 k]
          exact normal_mem k ⟨(12,13),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 15)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 15)) h)
        · change a k 17*normalRep k ⟨(15,14),by decide⟩ ∈ normalSpan k
          rw [extend_147_17 k]
          exact normal_mem k ⟨(12,14),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 15)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 15)) h)
        · change a k 17*normalRep k ⟨(15,15),by decide⟩ ∈ normalSpan k
          rw [extend_148_17 k]
          exact normal_mem k ⟨(12,15),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 15)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 15)) h)
        · change a k 17*normalRep k ⟨(15,16),by decide⟩ ∈ normalSpan k
          rw [extend_149_17 k]
          exact normal_mem k ⟨(12,16),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 15)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 15)) h)
        · change a k 17*normalRep k ⟨(15,17),by decide⟩ ∈ normalSpan k
          rw [extend_150_17 k]
          exact normal_mem k ⟨(12,17),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 15)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 15)) h)
      · exact False.elim ((by decide : ¬(Allowed 15 18 ∧ ((15,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 16)) h)
        · change a k 18*normalRep k ⟨(16,0),by decide⟩ ∈ normalSpan k
          rw [extend_151_18 k]
          exact normal_mem k ⟨(7,0),by decide⟩
        · change a k 19*normalRep k ⟨(16,0),by decide⟩ ∈ normalSpan k
          rw [extend_151_19 k]
          exact normal_mem k ⟨(14,0),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 16)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 16)) h)
        · change a k 18*normalRep k ⟨(16,1),by decide⟩ ∈ normalSpan k
          rw [extend_152_18 k]
          exact normal_mem k ⟨(7,1),by decide⟩
        · change a k 19*normalRep k ⟨(16,1),by decide⟩ ∈ normalSpan k
          rw [extend_152_19 k]
          exact normal_mem k ⟨(14,1),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 16)) h)
      · exact False.elim ((by decide : ¬(Allowed 16 2 ∧ ((16,2) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 16 3 ∧ ((16,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 16 4 ∧ ((16,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 16 5 ∧ ((16,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 16)) h)
        · change a k 18*normalRep k ⟨(16,6),by decide⟩ ∈ normalSpan k
          rw [extend_153_18 k]
          exact normal_mem k ⟨(7,6),by decide⟩
        · change a k 19*normalRep k ⟨(16,6),by decide⟩ ∈ normalSpan k
          rw [extend_153_19 k]
          exact normal_mem k ⟨(14,6),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 16)) h)
      · exact False.elim ((by decide : ¬(Allowed 16 7 ∧ ((16,7) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 16 8 ∧ ((16,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 16)) h)
        · change a k 18*normalRep k ⟨(16,9),by decide⟩ ∈ normalSpan k
          rw [extend_154_18 k]
          exact normal_mem k ⟨(7,9),by decide⟩
        · change a k 19*normalRep k ⟨(16,9),by decide⟩ ∈ normalSpan k
          rw [extend_154_19 k]
          exact normal_mem k ⟨(14,9),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 16)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 16)) h)
        · change a k 18*normalRep k ⟨(16,10),by decide⟩ ∈ normalSpan k
          rw [extend_155_18 k]
          exact normal_mem k ⟨(7,10),by decide⟩
        · change a k 19*normalRep k ⟨(16,10),by decide⟩ ∈ normalSpan k
          rw [extend_155_19 k]
          exact normal_mem k ⟨(14,10),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 16)) h)
      · exact False.elim ((by decide : ¬(Allowed 16 11 ∧ ((16,11) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 16 12 ∧ ((16,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 16)) h)
        · change a k 18*normalRep k ⟨(16,13),by decide⟩ ∈ normalSpan k
          rw [extend_156_18 k]
          exact normal_mem k ⟨(7,13),by decide⟩
        · change a k 19*normalRep k ⟨(16,13),by decide⟩ ∈ normalSpan k
          rw [extend_156_19 k]
          exact normal_mem k ⟨(14,13),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 16)) h)
      · exact False.elim ((by decide : ¬(Allowed 16 14 ∧ ((16,14) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 16 15 ∧ ((16,15) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 16)) h)
        · change a k 18*normalRep k ⟨(16,16),by decide⟩ ∈ normalSpan k
          rw [extend_157_18 k]
          exact normal_mem k ⟨(7,16),by decide⟩
        · change a k 19*normalRep k ⟨(16,16),by decide⟩ ∈ normalSpan k
          rw [extend_157_19 k]
          exact normal_mem k ⟨(14,16),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 16)) h)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 16)) h)
        · change a k 18*normalRep k ⟨(16,17),by decide⟩ ∈ normalSpan k
          rw [extend_158_18 k]
          exact normal_mem k ⟨(7,17),by decide⟩
        · change a k 19*normalRep k ⟨(16,17),by decide⟩ ∈ normalSpan k
          rw [extend_158_19 k]
          exact normal_mem k ⟨(14,17),by decide⟩
        · exact False.elim ((by decide : ¬(arrowSource 20=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 21=slotVertex 16)) h)
        · exact False.elim ((by decide : ¬(arrowSource 22=slotVertex 16)) h)
      · exact False.elim ((by decide : ¬(Allowed 16 18 ∧ ((16,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 17)) h)
        · change a k 20*normalRep k ⟨(17,0),by decide⟩ ∈ normalSpan k
          rw [extend_159_20 k]
          exact Submodule.zero_mem _
        · change a k 21*normalRep k ⟨(17,0),by decide⟩ ∈ normalSpan k
          rw [extend_159_21 k]
          exact normal_mem k ⟨(10,0),by decide⟩
        · change a k 22*normalRep k ⟨(17,0),by decide⟩ ∈ normalSpan k
          rw [extend_159_22 k]
          exact normal_mem k ⟨(13,0),by decide⟩
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 17)) h)
        · change a k 20*normalRep k ⟨(17,1),by decide⟩ ∈ normalSpan k
          rw [extend_160_20 k]
          exact Submodule.zero_mem _
        · change a k 21*normalRep k ⟨(17,1),by decide⟩ ∈ normalSpan k
          rw [extend_160_21 k]
          exact normal_mem k ⟨(10,1),by decide⟩
        · change a k 22*normalRep k ⟨(17,1),by decide⟩ ∈ normalSpan k
          rw [extend_160_22 k]
          exact normal_mem k ⟨(13,1),by decide⟩
      · exact False.elim ((by decide : ¬(Allowed 17 2 ∧ ((17,2) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 17 3 ∧ ((17,3) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 17 4 ∧ ((17,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 17 5 ∧ ((17,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 17)) h)
        · change a k 20*normalRep k ⟨(17,6),by decide⟩ ∈ normalSpan k
          rw [extend_161_20 k]
          exact Submodule.zero_mem _
        · change a k 21*normalRep k ⟨(17,6),by decide⟩ ∈ normalSpan k
          rw [extend_161_21 k]
          exact normal_mem k ⟨(10,6),by decide⟩
        · change a k 22*normalRep k ⟨(17,6),by decide⟩ ∈ normalSpan k
          rw [extend_161_22 k]
          exact normal_mem k ⟨(13,6),by decide⟩
      · exact False.elim ((by decide : ¬(Allowed 17 7 ∧ ((17,7) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 17 8 ∧ ((17,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 17)) h)
        · change a k 20*normalRep k ⟨(17,9),by decide⟩ ∈ normalSpan k
          rw [extend_162_20 k]
          exact Submodule.zero_mem _
        · change a k 21*normalRep k ⟨(17,9),by decide⟩ ∈ normalSpan k
          rw [extend_162_21 k]
          exact normal_mem k ⟨(10,9),by decide⟩
        · change a k 22*normalRep k ⟨(17,9),by decide⟩ ∈ normalSpan k
          rw [extend_162_22 k]
          exact normal_mem k ⟨(13,9),by decide⟩
      · exact False.elim ((by decide : ¬(Allowed 17 10 ∧ ((17,10) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 17 11 ∧ ((17,11) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 17 12 ∧ ((17,12) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 17 13 ∧ ((17,13) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 17 14 ∧ ((17,14) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 17 15 ∧ ((17,15) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 17 16 ∧ ((17,16) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 17)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 17)) h)
        · change a k 20*normalRep k ⟨(17,17),by decide⟩ ∈ normalSpan k
          rw [extend_163_20 k]
          exact normal_mem k ⟨(8,18),by decide⟩
        · change a k 21*normalRep k ⟨(17,17),by decide⟩ ∈ normalSpan k
          rw [extend_163_21 k]
          exact normal_mem k ⟨(10,17),by decide⟩
        · change a k 22*normalRep k ⟨(17,17),by decide⟩ ∈ normalSpan k
          rw [extend_163_22 k]
          exact normal_mem k ⟨(13,17),by decide⟩
      · exact False.elim ((by decide : ¬(Allowed 17 18 ∧ ((17,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
    · fin_cases j
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,0),by decide⟩ ∈ normalSpan k
          rw [extend_164_20 k]
          exact normal_mem k ⟨(8,0),by decide⟩
        · change a k 21*normalRep k ⟨(18,0),by decide⟩ ∈ normalSpan k
          rw [extend_164_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,0),by decide⟩ ∈ normalSpan k
          rw [extend_164_22 k]
          exact Submodule.zero_mem _
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,1),by decide⟩ ∈ normalSpan k
          rw [extend_165_20 k]
          exact normal_mem k ⟨(8,1),by decide⟩
        · change a k 21*normalRep k ⟨(18,1),by decide⟩ ∈ normalSpan k
          rw [extend_165_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,1),by decide⟩ ∈ normalSpan k
          rw [extend_165_22 k]
          exact Submodule.zero_mem _
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,2),by decide⟩ ∈ normalSpan k
          rw [extend_166_20 k]
          exact normal_mem k ⟨(8,2),by decide⟩
        · change a k 21*normalRep k ⟨(18,2),by decide⟩ ∈ normalSpan k
          rw [extend_166_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,2),by decide⟩ ∈ normalSpan k
          rw [extend_166_22 k]
          exact Submodule.zero_mem _
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,3),by decide⟩ ∈ normalSpan k
          rw [extend_167_20 k]
          exact normal_mem k ⟨(8,3),by decide⟩
        · change a k 21*normalRep k ⟨(18,3),by decide⟩ ∈ normalSpan k
          rw [extend_167_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,3),by decide⟩ ∈ normalSpan k
          rw [extend_167_22 k]
          exact Submodule.zero_mem _
      · exact False.elim ((by decide : ¬(Allowed 18 4 ∧ ((18,4) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · exact False.elim ((by decide : ¬(Allowed 18 5 ∧ ((18,5) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,6),by decide⟩ ∈ normalSpan k
          rw [extend_168_20 k]
          exact normal_mem k ⟨(8,6),by decide⟩
        · change a k 21*normalRep k ⟨(18,6),by decide⟩ ∈ normalSpan k
          rw [extend_168_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,6),by decide⟩ ∈ normalSpan k
          rw [extend_168_22 k]
          exact Submodule.zero_mem _
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,7),by decide⟩ ∈ normalSpan k
          rw [extend_169_20 k]
          exact normal_mem k ⟨(8,7),by decide⟩
        · change a k 21*normalRep k ⟨(18,7),by decide⟩ ∈ normalSpan k
          rw [extend_169_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,7),by decide⟩ ∈ normalSpan k
          rw [extend_169_22 k]
          exact Submodule.zero_mem _
      · exact False.elim ((by decide : ¬(Allowed 18 8 ∧ ((18,8) : Fin 19 × Fin 19) ≠ (18,18))) hc)
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,9),by decide⟩ ∈ normalSpan k
          rw [extend_170_20 k]
          exact normal_mem k ⟨(8,9),by decide⟩
        · change a k 21*normalRep k ⟨(18,9),by decide⟩ ∈ normalSpan k
          rw [extend_170_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,9),by decide⟩ ∈ normalSpan k
          rw [extend_170_22 k]
          exact Submodule.zero_mem _
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,10),by decide⟩ ∈ normalSpan k
          rw [extend_171_20 k]
          exact normal_mem k ⟨(8,10),by decide⟩
        · change a k 21*normalRep k ⟨(18,10),by decide⟩ ∈ normalSpan k
          rw [extend_171_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,10),by decide⟩ ∈ normalSpan k
          rw [extend_171_22 k]
          exact Submodule.zero_mem _
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,11),by decide⟩ ∈ normalSpan k
          rw [extend_172_20 k]
          exact normal_mem k ⟨(8,11),by decide⟩
        · change a k 21*normalRep k ⟨(18,11),by decide⟩ ∈ normalSpan k
          rw [extend_172_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,11),by decide⟩ ∈ normalSpan k
          rw [extend_172_22 k]
          exact Submodule.zero_mem _
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,12),by decide⟩ ∈ normalSpan k
          rw [extend_173_20 k]
          exact normal_mem k ⟨(8,12),by decide⟩
        · change a k 21*normalRep k ⟨(18,12),by decide⟩ ∈ normalSpan k
          rw [extend_173_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,12),by decide⟩ ∈ normalSpan k
          rw [extend_173_22 k]
          exact Submodule.zero_mem _
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,13),by decide⟩ ∈ normalSpan k
          rw [extend_174_20 k]
          exact normal_mem k ⟨(8,13),by decide⟩
        · change a k 21*normalRep k ⟨(18,13),by decide⟩ ∈ normalSpan k
          rw [extend_174_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,13),by decide⟩ ∈ normalSpan k
          rw [extend_174_22 k]
          exact Submodule.zero_mem _
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,14),by decide⟩ ∈ normalSpan k
          rw [extend_175_20 k]
          exact normal_mem k ⟨(8,14),by decide⟩
        · change a k 21*normalRep k ⟨(18,14),by decide⟩ ∈ normalSpan k
          rw [extend_175_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,14),by decide⟩ ∈ normalSpan k
          rw [extend_175_22 k]
          exact Submodule.zero_mem _
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,15),by decide⟩ ∈ normalSpan k
          rw [extend_176_20 k]
          exact normal_mem k ⟨(8,15),by decide⟩
        · change a k 21*normalRep k ⟨(18,15),by decide⟩ ∈ normalSpan k
          rw [extend_176_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,15),by decide⟩ ∈ normalSpan k
          rw [extend_176_22 k]
          exact Submodule.zero_mem _
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,16),by decide⟩ ∈ normalSpan k
          rw [extend_177_20 k]
          exact normal_mem k ⟨(8,16),by decide⟩
        · change a k 21*normalRep k ⟨(18,16),by decide⟩ ∈ normalSpan k
          rw [extend_177_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,16),by decide⟩ ∈ normalSpan k
          rw [extend_177_22 k]
          exact Submodule.zero_mem _
      · fin_cases b
        · exact False.elim ((by decide : ¬(arrowSource 0=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 1=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 2=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 3=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 4=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 5=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 6=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 7=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 8=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 9=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 10=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 11=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 12=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 13=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 14=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 15=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 16=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 17=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 18=slotVertex 18)) h)
        · exact False.elim ((by decide : ¬(arrowSource 19=slotVertex 18)) h)
        · change a k 20*normalRep k ⟨(18,17),by decide⟩ ∈ normalSpan k
          rw [extend_178_20 k]
          exact normal_mem k ⟨(8,17),by decide⟩
        · change a k 21*normalRep k ⟨(18,17),by decide⟩ ∈ normalSpan k
          rw [extend_178_21 k]
          exact Submodule.zero_mem _
        · change a k 22*normalRep k ⟨(18,17),by decide⟩ ∈ normalSpan k
          rw [extend_178_22 k]
          exact Submodule.zero_mem _
      · exact False.elim ((by decide : ¬(Allowed 18 18 ∧ ((18,18) : Fin 19 × Fin 19) ≠ (18,18))) hc)
  · rw [incompatible_normalRep k b c h]
    exact Submodule.zero_mem _
lemma e_mem (v : Fin 18) : e k v ∈ normalSpan k := by
  fin_cases v
  · exact normal_mem k ⟨(0,0),by decide⟩
  · exact normal_mem k ⟨(1,1),by decide⟩
  · exact normal_mem k ⟨(2,2),by decide⟩
  · exact normal_mem k ⟨(3,3),by decide⟩
  · exact normal_mem k ⟨(4,4),by decide⟩
  · exact normal_mem k ⟨(5,5),by decide⟩
  · exact normal_mem k ⟨(6,6),by decide⟩
  · exact normal_mem k ⟨(7,7),by decide⟩
  · exact normal_mem k ⟨(8,8),by decide⟩
  · exact normal_mem k ⟨(9,9),by decide⟩
  · exact normal_mem k ⟨(10,10),by decide⟩
  · exact normal_mem k ⟨(11,11),by decide⟩
  · exact normal_mem k ⟨(12,12),by decide⟩
  · exact normal_mem k ⟨(13,13),by decide⟩
  · exact normal_mem k ⟨(14,14),by decide⟩
  · exact normal_mem k ⟨(15,15),by decide⟩
  · exact normal_mem k ⟨(16,16),by decide⟩
  · exact normal_mem k ⟨(17,17),by decide⟩
lemma one_mem : (1 : Presented k) ∈ normalSpan k := by
  rw [← sum_e]
  exact Submodule.sum_mem _ (fun v _ => e_mem k v)
lemma left_stable (z : Presented k) (h : ∀ c, z*normalRep k c ∈ normalSpan k) :
    ∀ m ∈ normalSpan k, z*m ∈ normalSpan k := by
  intro m hm
  induction hm using Submodule.span_induction with
  | mem x hx => obtain ⟨c,rfl⟩ := hx; exact h c
  | zero => simpa using (normalSpan k).zero_mem
  | add x y hx hy ihx ihy => simpa [mul_add] using (normalSpan k).add_mem ihx ihy
  | smul r x hx ih => simpa [mul_smul_comm] using (normalSpan k).smul_mem r ih

def fromFree : Free k →ₐ[k] Presented k := (q k).comp (RingQuot.mkAlgHom k (PathRelations k))
lemma fromFree_surjective : Function.Surjective (fromFree k) :=
  (RingQuot.mkAlgHom_surjective k (Relations k)).comp (RingQuot.mkAlgHom_surjective k (PathRelations k))
lemma fromFree_stable (w : Free k) : ∀ m ∈ normalSpan k, fromFree k w*m ∈ normalSpan k := by
  induction w using FreeAlgebra.induction with
  | grade0 r =>
    intro m hm
    simpa [Algebra.smul_def] using (normalSpan k).smul_mem r hm
  | grade1 v =>
    cases v with
    | inl v => exact left_stable k (e k v) (vertex_span k v)
    | inr b => exact left_stable k (a k b) (arrow_span k b)
  | add x y hx hy =>
    intro m hm
    simpa [map_add,add_mul] using (normalSpan k).add_mem (hx m hm) (hy m hm)
  | mul x y hx hy =>
    intro m hm
    simpa [map_mul,mul_assoc] using hx _ (hy m hm)
lemma normalSpan_top : normalSpan k=⊤ := by
  apply top_unique
  intro y _
  obtain ⟨w,rfl⟩ := fromFree_surjective k y
  simpa using fromFree_stable k w 1 (one_mem k)
def normalLinear : (Coord → k) →ₗ[k] Presented k where
  toFun v := ∑ c, v c • normalRep k c
  map_add' v w := by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r v := by simp [Pi.smul_apply,Finset.smul_sum,smul_smul]
lemma normalLinear_single (c : Coord) : normalLinear k (Pi.single c 1)=normalRep k c := by
  simp [normalLinear,Pi.single_apply]
lemma normalLinear_surjective : Function.Surjective (normalLinear k) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← normalSpan_top k]
  apply Submodule.span_le.mpr
  rintro _ ⟨c,rfl⟩
  exact ⟨Pi.single c 1,normalLinear_single k c⟩
instance : Module.Finite k (Presented k) := Module.Finite.of_surjective (normalLinear k) (normalLinear_surjective k)
lemma evaluate_surjective : Function.Surjective (evaluate k) := by
  intro M
  obtain ⟨P,hP⟩ := pathMap_surjective k M
  exact ⟨q k P,hP⟩
theorem presented_dimension : Module.finrank k (Presented k)=179 := by
  apply le_antisymm
  · have h := LinearMap.finrank_le_finrank_of_surjective (normalLinear_surjective k)
    simpa [coordinate_count] using h
  · have h := LinearMap.finrank_le_finrank_of_surjective (show Function.Surjective (evaluate k).toLinearMap from evaluate_surjective k)
    simpa [end_dimension] using h
/-- Computational C2 certificate for the ten stated relations. -/
theorem C2_certificate : Function.Surjective (pathMap k) ∧
    (∀ x y, Relations k x y → pathMap k x=pathMap k y) ∧
    Module.finrank k (Presented k)=Module.finrank k (End k) := by
  exact ⟨pathMap_surjective k,fun _ _ h => respects k h,by rw [presented_dimension,end_dimension]⟩

end Presentation
end UniserialComputations.N5
