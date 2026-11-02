import N6Data
noncomputable section
namespace UniserialComputations.N6
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
/-- Actual ambient/source maps. The equations are literal equations in R;
π^(6-l) converts congruence in the target C_l into annihilation in R.
Rows/columns padded with C_0 represent zero summands. -/
structure HomData (i j : Fin 47) where
  M : Matrix (Fin 4) (Fin 4) R
  U : Matrix (Fin 2) (Fin 2) R
  ambient_descent : ∀ r c, π^(6-ambientLength i r)*π^(ambientLength j c)*M r c=0
  source_descent : ∀ r c, π^(6-sourceLength i r)*π^(sourceLength j c)*U r c=0
  commutes : ∀ r c, π^(6-ambientLength i r)*((M*embedding π j) r c-(embedding π i*U) r c)=0
include h6 in
lemma high_power (d : Nat) (hd : 6≤d) : π^d=0 := by
  obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hd
  rw [pow_add,h6,zero_mul]
include h6 ann in
lemma residue_pi : ρ π=0 := by
  apply (ann π).mp
  simpa only [← pow_succ] using h6
include ann in
theorem off_free_residue {i j : Fin 47} (f : HomData π i j) (r c : Fin 4)
    (hr : ambientLength i r=6) (hc : ambientLength j c≠6) : ρ (f.M r c)=0 := by
  apply (ann _).mp
  have hd := f.ambient_descent r c
  simp only [hr,Nat.sub_self,pow_zero,one_mul] at hd
  have hh := congrArg (fun x : R => π^(5-ambientLength j c)*x) hd
  have hl : ambientLength j c≤5 := by have := ambient_bounds j c; omega
  simpa only [← mul_assoc,← pow_add,Nat.sub_add_cancel hl,mul_zero] using hh

def reduceMatrix (i j : Fin 47) (M : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 2) (Fin 2) k :=
  fun r c => if r.val<freeRank i ∧ c.val<freeRank j then ρ (M (freeSlot i r) (freeSlot j c)) else 0
def reduceHom {i j : Fin 47} (f : HomData π i j) := reduceMatrix ρ i j f.M
/-- Definition of the factorization ideal via π⁵ annihilation of ambient maps. -/
def Equivalent {i j : Fin 47} (f g : HomData π i j) : Prop := ∀ r c,
  π^(6-ambientLength i r)*π^5*(f.M r c-g.M r c)=0
include h6 ann in
lemma quotient_free_entries {i j : Fin 47} (f g : HomData π i j) :
    Equivalent π f g ↔ ∀ r c, ambientLength i r=6 → ambientLength j c=6 → ρ (f.M r c)=ρ (g.M r c) := by
  constructor
  · intro h r c hr _
    have hh := h r c
    simpa [hr,ann,map_sub,sub_eq_zero] using hh
  · intro h r c
    by_cases hr : ambientLength i r=6
    · simp only [hr,Nat.sub_self,pow_zero,one_mul]
      rw [ann,map_sub,sub_eq_zero]
      by_cases hc : ambientLength j c=6
      · exact h r c hr hc
      · rw [off_free_residue π ρ ann f r c hr hc,off_free_residue π ρ ann g r c hr hc]
    · rw [← pow_add,high_power π h6 _ (by have := ambient_bounds i r; omega),zero_mul]
include h6 ann in
theorem quotient_exact {i j : Fin 47} (f g : HomData π i j) :
    Equivalent π f g ↔ reduceHom π ρ f=reduceHom π ρ g := by
  rw [quotient_free_entries π ρ h6 ann f g]
  constructor
  · intro h
    ext r c
    simp only [reduceHom,reduceMatrix]
    split_ifs with hh
    · exact h _ _ (free_slot_valid i r hh.1) (free_slot_valid j c hh.2)
    · rfl
  · intro h r c hr hc
    obtain ⟨a,ha,rfl⟩ := (free_slot_complete i r).mp hr
    obtain ⟨b,hb,rfl⟩ := (free_slot_complete j c).mp hc
    have hh := congrFun (congrFun h a) b
    simpa [reduceHom,reduceMatrix,ha,hb] using hh

theorem reduce_add (i j : Fin 47) (M N : Matrix (Fin 4) (Fin 4) R) :
    reduceMatrix ρ i j (M+N)=reduceMatrix ρ i j M+reduceMatrix ρ i j N := by
  ext r c
  simp only [reduceMatrix,Matrix.add_apply,map_add]
  split_ifs <;> simp

theorem reduce_scale (i j : Fin 47) (x : R) (M : Matrix (Fin 4) (Fin 4) R) :
    reduceMatrix ρ i j (x • M)=ρ x • reduceMatrix ρ i j M := by
  ext r c
  simp only [reduceMatrix,Matrix.smul_apply,smul_eq_mul,map_mul]
  split_ifs <;> simp
include h6 ann in
theorem pi_action_zero (i j : Fin 47) (M : Matrix (Fin 4) (Fin 4) R) :
    reduceMatrix ρ i j (π • M)=0 := by
  rw [reduce_scale,residue_pi π ρ h6 ann,zero_smul]
lemma sum_free_slots (o : Fin 47) (F : Fin 4 → k) :
    (∑ r, if ambientLength o r=6 then F r else 0) =
    ∑ a : Fin 2, if a.val<freeRank o then F (freeSlot o a) else 0 := by
  fin_cases o
  all_goals simp [ambientLength,freeRank,freeSlot,Fin.sum_univ_succ]
  all_goals ring
include ann in
theorem reduce_composition {i j l : Fin 47} (f : HomData π i j) (g : HomData π j l) :
    reduceMatrix ρ i l (f.M*g.M)=reduceHom π ρ f*reduceHom π ρ g := by
  ext a b
  by_cases ha : a.val<freeRank i
  · by_cases hb : b.val<freeRank l
    · simp only [reduceMatrix,reduceHom,Matrix.mul_apply,map_sum,map_mul]
      simp only [ha,hb,true_and,and_true,if_true]
      have hh : (∑ r : Fin 4, ρ (f.M (freeSlot i a) r)*ρ (g.M r (freeSlot l b))) =
          ∑ r : Fin 4, if ambientLength j r=6 then
            ρ (f.M (freeSlot i a) r)*ρ (g.M r (freeSlot l b)) else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases hr : ambientLength j r=6
        · simp [hr]
        · simp [hr,off_free_residue π ρ ann f _ r (free_slot_valid i a ha) hr]
      rw [hh,sum_free_slots]
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> simp
    · simp [reduceMatrix,reduceHom,Matrix.mul_apply,hb]
  · simp [reduceMatrix,reduceHom,Matrix.mul_apply,ha]

end UniserialComputations.N6
