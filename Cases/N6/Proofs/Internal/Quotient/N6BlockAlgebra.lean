import N6HomSpace
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
variable (k : Type*) [CommRing k]
theorem normal_cast (t : Fin 14) (A : Block ℤ) (ha : Normal ℤ t A) :
    Normal k t (fun r c => (A r c : k)) := by
  unfold Normal project param coords at *
  ext r c
  have h := congrArg (fun M : Block ℤ => (M r c : k)) ha
  simpa only [Fin.sum_univ_succ,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    basisBlock,Int.cast_id,Int.cast_add,Int.cast_mul,Fin.sum_univ_zero,Matrix.zero_apply,Int.cast_zero,add_zero] using h
theorem normal_basis_mul {a b c : Fin 14}
    (h : ∀ p q : Fin 3, Normal ℤ c (basisInt a p*basisInt b q)) (p q : Fin 3) :
    Normal k c (basisBlock k a p*basisBlock k b q) := by
  have hc := normal_cast k c _ (h p q)
  have he : (fun r s => ((basisInt a p*basisInt b q) r s : k)) =
      basisBlock k a p*basisBlock k b q := by
    ext r s
    simp [Matrix.mul_apply,basisBlock,Int.cast_sum,Int.cast_mul]
  rw [he] at hc
  exact hc
theorem normal_mul {a b c : Fin 14}
    (h : ∀ p q : Fin 3, Normal ℤ c (basisInt a p*basisInt b q))
    {A B : Block k} (ha : Normal k a A) (hb : Normal k b B) : Normal k c (A*B) := by
  have hae : A=param k a (coords k a A) := ha.symm
  have hbe : B=param k b (coords k b B) := hb.symm
  rw [hae,hbe]
  unfold param
  rw [Finset.sum_mul]
  apply normal_sum
  intro p
  rw [Finset.mul_sum]
  apply normal_sum
  intro q
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  exact normal_smul k _ (normal_basis_mul k h p q)
end UniserialComputations.N6
