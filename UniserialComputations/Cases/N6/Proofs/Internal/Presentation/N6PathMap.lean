import N6Insert
import N6PathPresentation
noncomputable section
namespace UniserialComputations.N6
namespace Presentation
set_option maxHeartbeats 400000
set_option maxRecDepth 20000
variable (k : Type*) [Field k]
def freeMap : Free k →ₐ[k] End k := FreeAlgebra.lift k (Sum.elim (vertex k) (arrow k))
lemma freeMap_respects {x y : Free k} (h : PathRelations k x y) : freeMap k x=freeMap k y := by
  cases h with
  | vv i j => simpa [freeMap,ev,apply_ite] using vertex_mul k i j
  | va i b => simpa [freeMap,ev,ea,apply_ite] using vertex_arrow k i b
  | av b i => simpa [freeMap,ev,ea,apply_ite] using arrow_vertex k b i
  | unit => simpa [freeMap,ev] using sum_vertex k
def pathMap : PathAlgebra k →ₐ[k] End k := RingQuot.liftAlgHom k ⟨freeMap k,fun _ _ h => freeMap_respects k h⟩
lemma pathMap_vertex (v : Fin 47) : pathMap k (pathVertex k v)=vertex k v := by rfl
lemma pathMap_arrow (b : Fin 75) : pathMap k (pathArrow k b)=arrow k b := by rfl
lemma path_va (i : Fin 47) (b : Fin 75) : pathVertex k i*pathArrow k b=if i=arrowTarget b then pathArrow k b else 0 :=
  by simpa only [pathVertex,pathArrow,map_mul,map_zero,apply_ite] using RingQuot.mkAlgHom_rel k (PathRelations.va (k:=k) i b)
lemma path_av (b : Fin 75) (i : Fin 47) : pathArrow k b*pathVertex k i=if i=arrowSource b then pathArrow k b else 0 :=
  by simpa only [pathVertex,pathArrow,map_mul,map_zero,apply_ite] using RingQuot.mkAlgHom_rel k (PathRelations.av (k:=k) b i)
lemma word_anchor (s t : Fin 47) (p : List (Fin 75)) (hp : walkEnd s p=some t) (hn : p≠[]) :
    word (pathArrow k) p*pathVertex k s=word (pathArrow k) p := by
  cases p with
  | nil => contradiction
  | cons b p =>
    simp only [walkEnd] at hp
    split_ifs at hp with hb
    · have hw : word (pathArrow k) (b::p)=word (pathArrow k) p*pathArrow k b := by
        simp [word,List.reverse_cons,List.prod_append]
      rw [hw,mul_assoc,path_av,if_pos hb.symm]
/-- Local matrix of a path, including its source idempotent for an empty path. -/
def localWalk (K : Type*) [CommRing K] (s : Fin 47) (p : List (Fin 75)) : Block K := wordMatrix K p*unitBlock K s
lemma localWalk_snoc (K : Type*) [CommRing K] (s : Fin 47) (p : List (Fin 75)) (b : Fin 75) :
    localWalk K s (p++[b])=arrowMatrix K b*localWalk K s p := by
  change word (arrowMatrix K) (p++[b])*unitBlock K s=_
  rw [word_snoc,mul_assoc]
  rfl
lemma localWalk_normal (s t : Fin 47) (p : List (Fin 75)) (hp : walkEnd s p=some t) :
    Normal k (homKind t s) (localWalk k s p) := by
  induction p using List.reverseRecOn generalizing t with
  | nil =>
    have ht : s=t := Option.some.inj hp
    subst t
    simpa [localWalk,wordMatrix] using unit_normal k s
  | append_singleton p b ih =>
    rw [walkEnd_append] at hp
    cases h : walkEnd s p with
    | none => simp [h] at hp
    | some u =>
      simp only [h,Option.bind_some,walkEnd] at hp
      split_ifs at hp with hb
      · have ht : arrowTarget b=t := Option.some.inj hp
        subst t
        rw [localWalk_snoc]
        have ha : Normal k (homKind (arrowTarget b) u) (arrowMatrix k b) := by simpa only [hb] using arrow_normal k b
        exact normal_mul k (allowed_products _ _ _ (kind_allowed (arrowTarget b) u s)) ha (ih u h)
lemma pathMap_walk (s t : Fin 47) (p : List (Fin 75)) (hp : walkEnd s p=some t) :
    (pathMap k (word (pathArrow k) p*pathVertex k s)).val=insert k t s (localWalk k s p) := by
  induction p using List.reverseRecOn generalizing t with
  | nil =>
    have ht : s=t := Option.some.inj hp
    subst t
    simp [word,localWalk,wordMatrix,pathMap_vertex,vertex,insertHom]
  | append_singleton p b ih =>
    rw [walkEnd_append] at hp
    cases h : walkEnd s p with
    | none => simp [h] at hp
    | some u =>
      simp only [h,Option.bind_some,walkEnd] at hp
      split_ifs at hp with hb
      · have ht : arrowTarget b=t := Option.some.inj hp
        subst t
        rw [word_snoc,mul_assoc,map_mul,pathMap_arrow]
        change insert k (arrowTarget b) (arrowSource b) (arrowMatrix k b)*_=_
        rw [ih u h,insert_mul k _ _ _ _ _ _ (normal_padded k _ _ (arrow_normal k b)) (normal_padded k _ _ (localWalk_normal k s u p h)),if_pos hb,localWalk_snoc]
lemma insert_list_sum (i j : Fin 47) (xs : List (Block k)) : insert k i j xs.sum=(xs.map (insert k i j)).sum := by
  induction xs with
  | nil => exact insert_zero k i j
  | cons x xs ih => simp only [List.sum_cons,List.map_cons,insert_add,ih]
lemma insert_map_sum (i j : Fin 47) {ι : Type*} (xs : List ι) (f : ι → Block k) :
    (xs.map (fun x => insert k i j (f x))).sum=insert k i j (xs.map f).sum := by
  rw [insert_list_sum]
  simp only [List.map_map,Function.comp_def]
lemma insert_zsmul (i j : Fin 47) (c : Int) (B : Block k) : insert k i j (c • B)=c • insert k i j B := by
  simpa only [Int.cast_smul_eq_zsmul] using insert_smul k i j (c:k) B
def pathMatrixMap : PathAlgebra k →ₐ[k] TotalMatrix k := (endAlgebra k).val.comp (pathMap k)
lemma relation_image (z : Fin 47) : pathMap k (polynomial (pathArrow k) (relationTerms z))=0 := by
  apply Subtype.ext
  have he := relation_endpoints z
  have hn := relation_minimum_degree z
  have ht (u : Int × List (Fin 75)) (hu : u ∈ relationTerms z) :
      (pathMap k (word (pathArrow k) u.2)).val=insert k (relationTarget z) (relationSource z) (localWalk k (relationSource z) u.2) := by
    have hp : walkEnd (relationSource z) u.2=some (relationTarget z) := by
      simpa using List.all_eq_true.mp he u hu
    have hlen : 2≤u.2.length := by simpa using List.all_eq_true.mp hn u hu
    rw [← word_anchor k _ _ _ hp (by intro hh; simp [hh] at hlen)]
    exact pathMap_walk k _ _ _ hp
  change pathMatrixMap k (polynomial (pathArrow k) (relationTerms z))=0
  simp only [polynomial,map_list_sum,List.map_map,Function.comp_def,map_zsmul]
  change ((relationTerms z).map (fun u => u.1 • (pathMap k (word (pathArrow k) u.2)).val)).sum=0
  rw [List.map_congr_left (fun u hu => congrArg (fun x : TotalMatrix k => u.1 • x) (ht u hu))]
  simp only [← insert_zsmul]
  rw [insert_map_sum k (relationTarget z) (relationSource z) (relationTerms z) (fun u => u.1 • localWalk k (relationSource z) u.2)]
  have hh : ((relationTerms z).map (fun u => u.1 • localWalk k (relationSource z) u.2)).sum=0 := by
    have hd : ∀ ts : List (Int × List (Fin 75)), (ts.map (fun u => u.1 • localWalk k (relationSource z) u.2)).sum=(ts.map (fun u => u.1 • wordMatrix k u.2)).sum*unitBlock k (relationSource z) := by
      intro ts; induction ts with
      | nil => simp
      | cons u ts ih =>
        simp only [List.map_cons,List.sum_cons,add_mul]
        rw [← ih]
        congr 1
        exact (smul_mul_assoc u.1 (wordMatrix k u.2) (unitBlock k (relationSource z))).symm
    rw [hd]
    have hz : ((relationTerms z).map (fun u => u.1 • wordMatrix k u.2)).sum=0 := by
      simpa only [relationValue,Int.cast_smul_eq_zsmul] using relations_vanish k z
    rw [hz,zero_mul]
  rw [hh,insert_zero]
lemma respects {x y : PathAlgebra k} (h : Relations k x y) : pathMap k x=pathMap k y := by
  cases h with
  | relation z => simpa only [map_zero] using relation_image k z
def evaluate : Presented k →ₐ[k] End k := RingQuot.liftAlgHom k ⟨pathMap k,fun _ _ h => respects k h⟩
lemma evaluate_q (x : PathAlgebra k) : evaluate k (q k x)=pathMap k x := by rfl
lemma evaluate_walk (s t : Fin 47) (p : List (Fin 75)) (hp : walkEnd s p=some t) :
    (evaluate k (walk k s p)).val=insert k t s (localWalk k s p) := by
  have hq : walk k s p=q k (word (pathArrow k) p*pathVertex k s) := by
    simp only [walk,word,e,a,map_mul,map_list_prod,List.map_map,Function.comp_def]
    rfl
  rw [hq,evaluate_q]
  exact pathMap_walk k s t p hp
end Presentation
end UniserialComputations.N6
