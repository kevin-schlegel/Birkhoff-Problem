import N5Computations
noncomputable section
namespace UniserialComputations.N5
namespace C3
set_option maxHeartbeats 5000000
def ambientLength : Fin 12 → Fin 3 → Nat := ![![5,2,0],![5,2,0],![5,3,0],![5,3,0],![5,3,0],![5,3,1],![5,3,1],![5,3,1],![5,3,2],![5,3,2],![5,4,2],![5,4,2]]
def sourceLength : Fin 12 → Fin 2 → Nat := ![![3,1],![4,1],![3,1],![4,1],![4,2],![4,2],![3,1],![3,2],![3,1],![4,2],![3,2],![4,2]]
def generatorExponent : Fin 12 → Fin 3 → Fin 2 → Nat := ![![![2,5],![0,1],![5,5]],![![1,5],![0,1],![5,5]],![![2,5],![1,2],![5,5]],![![1,5],![0,2],![5,5]],![![1,5],![0,1],![5,5]],![![1,5],![0,1],![5,0]],![![2,5],![1,2],![0,5]],![![2,5],![1,1],![5,0]],![![2,5],![1,5],![0,1]],![![1,5],![0,1],![5,1]],![![5,3],![1,5],![0,1]],![![1,5],![5,2],![0,1]]]
theorem ambient_bounds : ∀ o i, ambientLength o i ≤ 5 := by decide
theorem first_free : ∀ o, ambientLength o 0=5 := by decide
theorem other_torsion : ∀ o i, i≠0 → ambientLength o i≤4 := by decide
theorem source_bounds : ∀ o i, sourceLength o i≤5 := by decide
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h5 : π^5=0) (ann : ∀ r, π^4*r=0 ↔ ρ r=0)
def embedding (o : Fin 12) : Matrix (Fin 3) (Fin 2) R := fun i j => π^(generatorExponent o i j)
/-- Literal annihilation congruences for ambient/source maps and their commuting square.
Multiplication by π^(5-l) converts equality in C_l to equality in R. -/
structure HomData (o : Fin 12) where
  M : Matrix (Fin 3) (Fin 3) R
  U : Matrix (Fin 2) (Fin 2) R
  ambient_descent : ∀ i j, π^(5-ambientLength o i)*π^(ambientLength o j)*M i j=0
  source_descent : ∀ i j, π^(5-sourceLength o i)*π^(sourceLength o j)*U i j=0
  preserves : ∀ i j, π^(5-ambientLength o i)*((M*embedding π o) i j-(embedding π o*U) i j)=0

include h5 in
lemma high_power_zero (m : Nat) (hm : 5≤m) : π^m=0 := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add,h5,zero_mul]

include h5 in
def diagonal (o : Fin 12) (r : R) : HomData π o where
  M := Matrix.scalar _ r
  U := Matrix.scalar _ r
  ambient_descent := by
    intro i j
    by_cases hij : i=j
    · subst j
      simp only [Matrix.scalar_apply,Matrix.diagonal_apply_eq]
      rw [← pow_add,Nat.sub_add_cancel (ambient_bounds o i),h5,zero_mul]
    · simp [Matrix.scalar_apply,Matrix.diagonal_apply_ne _ hij]
  source_descent := by
    intro i j
    by_cases hij : i=j
    · subst j
      simp only [Matrix.scalar_apply,Matrix.diagonal_apply_eq]
      rw [← pow_add,Nat.sub_add_cancel (source_bounds o i),h5,zero_mul]
    · simp [Matrix.scalar_apply,Matrix.diagonal_apply_ne _ hij]
  preserves := by
    intro i j
    simp [Matrix.scalar_apply,Matrix.mul_apply,Matrix.diagonal_apply,mul_comm]

include ann in
theorem off_residue {o : Fin 12} (f : HomData π o) (j : Fin 3) (hj : j≠0) : ρ (f.M 0 j)=0 := by
  apply (ann _).mp
  have hd := f.ambient_descent 0 j
  simp only [first_free,Nat.sub_self,pow_zero,one_mul] at hd
  have he := congrArg (fun x : R => π^(4-ambientLength o j)*x) hd
  simpa only [← mul_assoc,← pow_add,Nat.sub_add_cancel (other_torsion o j hj),mul_zero] using he

/-- The factorization ideal, defined by π⁴ annihilation of every ambient component. -/
def Equivalent {o : Fin 12} (f g : HomData π o) : Prop :=
  ∀ i j, π^(5-ambientLength o i)*π^4*(f.M i j-g.M i j)=0

include h5 ann in
theorem quotient_exact {o : Fin 12} (f g : HomData π o) :
    Equivalent π f g ↔ ρ (f.M 0 0)=ρ (g.M 0 0) := by
  constructor
  · intro h
    have hh := h 0 0
    simpa [first_free,ann,map_sub,sub_eq_zero] using hh
  · intro h i j
    by_cases hi : i=0
    · subst i
      simp only [first_free,Nat.sub_self,pow_zero,one_mul]
      rw [ann,map_sub,sub_eq_zero]
      by_cases hj : j=0
      · subst j; exact h
      · rw [off_residue π ρ ann f j hj,off_residue π ρ ann g j hj]
    · rw [← pow_add, high_power_zero π h5 _ (by have := other_torsion o i hi; omega),zero_mul]

include ann in
theorem composition {o : Fin 12} (f g : HomData π o) :
    ρ ((f.M*g.M) 0 0)=ρ (f.M 0 0)*ρ (g.M 0 0) := by
  simp [Matrix.mul_apply,Fin.sum_univ_succ,off_residue π ρ ann f 1 (by decide),off_residue π ρ ann f 2 (by decide)]

include h5 in
theorem surjective (surj : Function.Surjective ρ) (o : Fin 12) :
    Function.Surjective (fun f : HomData π o => ρ (f.M 0 0)) := by
  intro a
  obtain ⟨r,hr⟩ := surj a
  exact ⟨diagonal π h5 o r, by simpa [diagonal] using hr⟩

include h5 in
theorem local_certificate (surj : Function.Surjective ρ) {o : Fin 12} (f : HomData π o) :
    ∃ g : HomData π o,
      (ρ (f.M 0 0)*ρ (g.M 0 0)=1 ∧ ρ (g.M 0 0)*ρ (f.M 0 0)=1) ∨
      ((1-ρ (f.M 0 0))*ρ (g.M 0 0)=1 ∧ ρ (g.M 0 0)*(1-ρ (f.M 0 0))=1) := by
  by_cases h : ρ (f.M 0 0)=0
  · exact ⟨diagonal π h5 o 1, Or.inr (by simp [h,diagonal])⟩
  · obtain ⟨r,hr⟩ := surj ((ρ (f.M 0 0))⁻¹)
    exact ⟨diagonal π h5 o r, Or.inl (by simp [diagonal,hr,h])⟩
end C3
end UniserialComputations.N5
