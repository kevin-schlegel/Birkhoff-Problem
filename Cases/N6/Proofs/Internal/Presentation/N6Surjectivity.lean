import N6ImageCertificate
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 400000
set_option maxRecDepth 20000
variable (k : Type*) [Field k]
def evalMatrix : Presented k →ₐ[k] TotalMatrix k := (endAlgebra k).val.comp (evaluate k)
lemma evalMatrix_apply (x : Presented k) : evalMatrix k x=(evaluate k x).val := rfl
def basisPathLift (i j : Fin 47) (b : Fin 3) : Presented k :=
  ((basisPaths i j b).map (fun u => u.1 • normalRep k u.2)).sum
lemma basisPathLift_image (i j : Fin 47) (b : Fin 3) :
    evalMatrix k (basisPathLift k i j b)=insert k i j (basisBlock k (homKind i j) b) := by
  have hc := basis_paths_certificate i j b
  have ht (u : Int × Fin 1708) (hu : u ∈ basisPaths i j b) : normalTarget u.2=i ∧ normalSource u.2=j := by
    simpa using List.all_eq_true.mp hc.2 u hu
  have he (u : Int × Fin 1708) (hu : u ∈ basisPaths i j b) :
      evalMatrix k (normalRep k u.2)=insert k i j (castBlock k (normalBlock u.2)) := by
    change (evaluate k (normalRep k u.2)).val=_
    rw [normal_image,(ht u hu).1,(ht u hu).2]
  simp only [basisPathLift,map_list_sum,List.map_map,Function.comp_def,map_zsmul]
  rw [List.map_congr_left (fun u hu => congrArg (fun x : TotalMatrix k => u.1 • x) (he u hu))]
  simp only [← insert_zsmul]
  rw [insert_map_sum k i j (basisPaths i j b) (fun u => u.1 • castBlock k (normalBlock u.2))]
  congr 1
  have hh := congrArg (castBlock k) hc.1
  simpa only [map_list_sum,map_zsmul,List.map_map,Function.comp_def,castBlock_basis] using hh
lemma insert_sum (i j : Fin 47) {ι : Type*} [Fintype ι] (f : ι → Block k) :
    insert k i j (∑ x,f x)=∑ x,insert k i j (f x) := by
  classical
  let L : Block k →ₗ[k] TotalMatrix k :=
    {toFun := insert k i j, map_add' := insert_add k i j, map_smul' := insert_smul k i j}
  exact map_sum L f Finset.univ
def liftBlock (i j : Fin 47) (B : Block k) : Presented k :=
  ∑ b : Fin 3, coords k (homKind i j) B b • basisPathLift k i j b
lemma liftBlock_image (i j : Fin 47) (B : Block k) (hB : Normal k (homKind i j) B) :
    evalMatrix k (liftBlock k i j B)=insert k i j B := by
  simp only [liftBlock,map_sum,map_smul,basisPathLift_image]
  simp only [← insert_smul]
  rw [← insert_sum]
  exact congrArg (insert k i j) hB
lemma sum_insert_blocks (A : TotalMatrix k) : (∑ i : Fin 47, ∑ j : Fin 47, insert k i j (block k A i j))=A := by
  ext r c
  simp only [Matrix.sum_apply]
  rw [Finset.sum_eq_single r.1]
  · rw [Finset.sum_eq_single c.1]
    · simp [insert,assemble,block,part]
    · intro j _ hne
      simp [insert,assemble,Ne.symm hne]
    · simp
  · intro i _ hne
    apply Finset.sum_eq_zero
    intro j _
    simp [insert,assemble,Ne.symm hne]
  · simp
def liftEnd (A : End k) : Presented k := ∑ i : Fin 47, ∑ j : Fin 47, liftBlock k i j (block k A.val i j)
lemma liftEnd_spec (A : End k) : evaluate k (liftEnd k A)=A := by
  apply Subtype.ext
  rw [← evalMatrix_apply]
  simp only [liftEnd,map_sum]
  apply Eq.trans ?_ (sum_insert_blocks k A.val)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact liftBlock_image k i j _ (A.property i j)
theorem evaluate_surjective : Function.Surjective (evaluate k) := fun A => ⟨liftEnd k A,liftEnd_spec k A⟩
theorem pathMap_surjective : Function.Surjective (pathMap k) := by
  intro A
  obtain ⟨x,hx⟩ := evaluate_surjective k A
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective k (Relations k) x
  exact ⟨p,hx⟩
end UniserialComputations.N6.Presentation
