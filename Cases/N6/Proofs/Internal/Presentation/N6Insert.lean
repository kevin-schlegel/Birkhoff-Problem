import N6EndAlgebra
import N6QuiverData
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 400000
set_option maxRecDepth 20000
variable (k : Type*) [Field k]
lemma block_ext {A B : TotalMatrix k} (h : ∀ i j,block k A i j=block k B i j) : A=B := by
  rw [← assemble_block k A,← assemble_block k B]
  congr 1
  funext i j
  exact h i j
def insert (i j : Fin 47) (B : Block k) : TotalMatrix k :=
  assemble k (fun x y => if x=i ∧ y=j then B else 0)
lemma block_insert (i j : Fin 47) (B : Block k) (hB : Padded k i j B) (x y : Fin 47) :
    block k (insert k i j B) x y=if x=i ∧ y=j then B else 0 := by
  apply block_assemble
  intro u v
  split_ifs with h
  · obtain ⟨rfl,rfl⟩ := h; exact hB
  · intro r c _; rfl
lemma insert_add (i j : Fin 47) (A B : Block k) : insert k i j (A+B)=insert k i j A+insert k i j B := by
  ext r c
  simp only [insert,assemble,Matrix.add_apply]
  split_ifs <;> simp
lemma insert_smul (i j : Fin 47) (a : k) (B : Block k) : insert k i j (a • B)=a • insert k i j B := by
  ext r c
  simp only [insert,assemble,Matrix.smul_apply]
  split_ifs <;> simp
lemma insert_zero (i j : Fin 47) : insert k i j 0=0 := by
  ext r c; simp [insert,assemble]
lemma padded_mul (i j l m : Fin 47) (A B : Block k) (hA : Padded k i j A) (hB : Padded k l m B) : Padded k i m (A*B) := by
  intro r c h
  rcases not_and_or.mp h with hr|hc
  · simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro q _
    rw [hA r q (by simp [hr]),zero_mul]
  · simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro q _
    rw [hB q c (by simp [hc]),mul_zero]
lemma insert_mul (i j l m : Fin 47) (A B : Block k) (hA : Padded k i j A) (hB : Padded k l m B) :
    insert k i j A*insert k l m B=if j=l then insert k i m (A*B) else 0 := by
  apply block_ext k
  intro x y
  rw [block_mul]
  simp only [block_insert k i j A hA,block_insert k l m B hB]
  by_cases hj : j=l
  · subst l
    rw [if_pos rfl,block_insert k i m (A*B) (padded_mul k i j j m A B hA hB)]
    by_cases hx : x=i <;> by_cases hy : y=m <;> simp [hx,hy]
  · rw [if_neg hj,block_zero]
    by_cases hx : x=i <;> by_cases hy : y=m <;> simp [hx,hy,hj,Ne.symm hj]
lemma unitBlock_diagonal (i : Fin 47) : unitBlock k i=Matrix.diagonal (fun r : Fin 2 => if r.val<freeRank i then 1 else 0) := by
  ext r c
  by_cases h : r=c <;> simp [unitBlock,Matrix.diagonal_apply,h]
lemma unit_mul (i j : Fin 47) (A : Block k) (h : Padded k i j A) : unitBlock k i*A=A := by
  rw [unitBlock_diagonal]
  ext r c
  rw [Matrix.diagonal_mul]
  by_cases hr : r.val<freeRank i
  · simp [hr]
  · simp [hr,h r c (by simp [hr])]
lemma mul_unit (i j : Fin 47) (A : Block k) (h : Padded k i j A) : A*unitBlock k j=A := by
  rw [unitBlock_diagonal]
  ext r c
  rw [Matrix.mul_diagonal]
  by_cases hc : c.val<freeRank j
  · simp [hc]
  · simp [hc,h r c (by simp [hc])]
def insertHom (i j : Fin 47) (B : homSpace k (homKind i j)) : End k :=
  ⟨insert k i j B.val,by
    intro x y
    rw [block_insert k i j B.val (normal_padded k i j B.property)]
    split_ifs with h
    · obtain ⟨rfl,rfl⟩ := h; exact B.property
    · exact normal_zero k _⟩
def vertex (v : Fin 47) : End k := insertHom k v v ⟨unitBlock k v,unit_normal k v⟩
lemma arrow_normal_int : ∀ a : Fin 75, Normal ℤ (homKind (arrowTarget a) (arrowSource a)) (arrowMatrix ℤ a) := by decide +kernel
set_option maxHeartbeats 8000000 in
lemma arrow_normal (a : Fin 75) : Normal k (homKind (arrowTarget a) (arrowSource a)) (arrowMatrix k a) := by
  have h := normal_cast k _ _ (arrow_normal_int a)
  have he : (fun r c => (arrowMatrix ℤ a r c : k))=arrowMatrix k a := by
    fin_cases a <;> ext r c <;> fin_cases r <;> fin_cases c <;> norm_num [arrowMatrix]
  rw [he] at h
  exact h
def arrow (a : Fin 75) : End k := insertHom k (arrowTarget a) (arrowSource a) ⟨arrowMatrix k a,arrow_normal k a⟩
lemma vertex_mul (i j : Fin 47) : vertex k i*vertex k j=if i=j then vertex k i else 0 := by
  apply Subtype.ext
  change insert k i i (unitBlock k i)*insert k j j (unitBlock k j)=_
  rw [insert_mul k _ _ _ _ _ _ (normal_padded k _ _ (unit_normal k i)) (normal_padded k _ _ (unit_normal k j))]
  by_cases h : i=j
  · subst j
    simp only [if_pos rfl,unit_mul k i i _ (normal_padded k _ _ (unit_normal k i))]
    rfl
  · simp [h]
lemma vertex_arrow (i : Fin 47) (b : Fin 75) : vertex k i*arrow k b=if i=arrowTarget b then arrow k b else 0 := by
  apply Subtype.ext
  change insert k i i (unitBlock k i)*insert k (arrowTarget b) (arrowSource b) (arrowMatrix k b)=_
  rw [insert_mul k _ _ _ _ _ _ (normal_padded k _ _ (unit_normal k i)) (normal_padded k _ _ (arrow_normal k b))]
  by_cases h : i=arrowTarget b
  · subst i
    simp only [if_pos rfl,unit_mul k _ _ _ (normal_padded k _ _ (arrow_normal k b))]
    rfl
  · simp [h]
lemma arrow_vertex (b : Fin 75) (i : Fin 47) : arrow k b*vertex k i=if i=arrowSource b then arrow k b else 0 := by
  apply Subtype.ext
  change insert k (arrowTarget b) (arrowSource b) (arrowMatrix k b)*insert k i i (unitBlock k i)=_
  rw [insert_mul k _ _ _ _ _ _ (normal_padded k _ _ (arrow_normal k b)) (normal_padded k _ _ (unit_normal k i))]
  by_cases h : i=arrowSource b
  · subst i
    simp only [if_pos rfl,mul_unit k _ _ _ (normal_padded k _ _ (arrow_normal k b))]
    rfl
  · simp [h,Ne.symm h]
lemma sum_vertex : ∑ v,vertex k v=1 := by
  apply Subtype.ext
  apply block_ext k
  intro i j
  change block k (∑ v,insert k v v (unitBlock k v)) i j=block k 1 i j
  have hs : ∀ s : Finset (Fin 47), block k (∑ v ∈ s,insert k v v (unitBlock k v)) i j=∑ v ∈ s,block k (insert k v v (unitBlock k v)) i j := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [block_zero]
    | @insert v s hv ih => simpa [Finset.sum_insert,hv,block_add] using congrArg (fun x => block k (insert k v v (unitBlock k v)) i j+x) ih
  rw [hs,block_one]
  simp only [block_insert k _ _ _ (normal_padded k _ _ (unit_normal k _))]
  by_cases h : i=j
  · subst j; simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro v _
    exact if_neg (by rintro ⟨hi,hj⟩; exact h (hi.trans hj.symm))
end UniserialComputations.N6
