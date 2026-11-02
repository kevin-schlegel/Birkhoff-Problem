import N6HomSpace
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
abbrev Slot := Σ i : Fin 47, Fin (freeRank i)
def part (i : Fin 47) (r : Fin (freeRank i)) : Fin 2 := ⟨r.val,lt_of_lt_of_le r.isLt (rank_bounds i).2⟩
theorem slot_count : Fintype.card Slot=61 := by decide
variable (k : Type*) [CommRing k]
abbrev TotalMatrix := Matrix Slot Slot k
def block (A : TotalMatrix k) (i j : Fin 47) : Block k := fun r c =>
  if h : r.val<freeRank i ∧ c.val<freeRank j then
    A ⟨i,⟨r.val,h.1⟩⟩ ⟨j,⟨c.val,h.2⟩⟩ else 0
def assemble (F : Fin 47 → Fin 47 → Block k) : TotalMatrix k :=
  fun r c => F r.1 c.1 (part r.1 r.2) (part c.1 c.2)
def Padded (i j : Fin 47) (A : Block k) : Prop :=
  ∀ r c, ¬(r.val<freeRank i ∧ c.val<freeRank j) → A r c=0
theorem block_assemble (F : Fin 47 → Fin 47 → Block k) (h : ∀ i j,Padded k i j (F i j)) (i j : Fin 47) :
    block k (assemble k F) i j=F i j := by
  ext r c
  dsimp [block]
  split_ifs with hh
  · rfl
  · exact (h i j r c hh).symm
theorem assemble_block (A : TotalMatrix k) : assemble k (block k A)=A := by
  ext r c
  simp [assemble,block,part,r.2.isLt,c.2.isLt]
theorem block_add (A B : TotalMatrix k) (i j : Fin 47) : block k (A+B) i j=block k A i j+block k B i j := by
  ext r c
  simp only [block,Matrix.add_apply]
  split_ifs <;> simp
theorem block_smul (x : k) (A : TotalMatrix k) (i j : Fin 47) : block k (x • A) i j=x • block k A i j := by
  ext r c
  simp only [block,Matrix.smul_apply]
  split_ifs <;> simp
theorem block_zero (i j : Fin 47) : block k (0 : TotalMatrix k) i j=0 := by
  ext r c; simp [block]
theorem block_padded (A : TotalMatrix k) (i j : Fin 47) : Padded k i j (block k A i j) := by
  intro r c h; simp [block,h]
theorem sum_small (m : Nat) (hm : m≤2) (F : Fin 2 → k) :
    (∑ r : Fin m, F ⟨r.val,lt_of_lt_of_le r.isLt hm⟩) = ∑ r : Fin 2, if r.val<m then F r else 0 := by
  interval_cases m <;> simp [Fin.sum_univ_succ]
theorem sum_parts (i : Fin 47) (F : Fin 2 → k) :
    (∑ r : Fin (freeRank i), F (part i r)) = ∑ r : Fin 2, if r.val<freeRank i then F r else 0 :=
  sum_small k (freeRank i) (rank_bounds i).2 F
theorem block_mul (A B : TotalMatrix k) (i j : Fin 47) :
    block k (A*B) i j=∑ l : Fin 47, block k A i l*block k B l j := by
  ext r c
  simp only [Matrix.sum_apply,Matrix.mul_apply]
  by_cases hh : r.val<freeRank i ∧ c.val<freeRank j
  · let x : Slot := ⟨i,⟨r.val,hh.1⟩⟩
    let y : Slot := ⟨j,⟨c.val,hh.2⟩⟩
    conv_lhs => simp [block,hh,Matrix.mul_apply,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro l _
    have hs := sum_parts k l (fun s => block k A i l r s*block k B l j s c)
    have hl : (∑ s : Fin (freeRank l), block k A i l r (part l s)*block k B l j (part l s) c)=
        ∑ s : Fin (freeRank l), A x ⟨l,s⟩*B ⟨l,s⟩ y := by
      apply Finset.sum_congr rfl
      intro s _
      simp [block,part,hh.1,hh.2,s.isLt,x,y]
    rw [hl] at hs
    rw [hs]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : s.val<freeRank l
    · simp [h]
    · simp [block,h]
  · have hbad : ¬r.val<freeRank i ∨ ¬c.val<freeRank j := not_and_or.mp hh
    rcases hbad with hr|hc
    · simp [block,Matrix.mul_apply,hr]
    · simp [block,Matrix.mul_apply,hc]
end UniserialComputations.N6
