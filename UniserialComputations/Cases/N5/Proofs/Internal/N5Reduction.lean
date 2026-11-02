import N5Lifts
noncomputable section
namespace UniserialComputations.N5.Raw
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h5 : π^5=0) (ann : ∀ r, π^4*r=0 ↔ ρ r=0)
include h5 ann in
lemma residue_pi : ρ π=0 := by
  apply (ann π).mp
  simpa only [← pow_succ] using h5
lemma equation_add (i j : Fin 18) (v w : Fin 13 → R) (r : Fin 3) (c : Fin 2) :
    equation π i j (v+w) r c=equation π i j v r c+equation π i j w r c := by
  simp only [equation,ambient,source,Matrix.mul_apply,Fin.sum_univ_succ,Pi.add_apply]
  ring
lemma equation_smul (i j : Fin 18) (v : Fin 13 → R) (x : R) (r : Fin 3) (c : Fin 2) :
    equation π i j (fun z => x*v z) r c=x*equation π i j v r c := by
  simp only [equation,ambient,source,Matrix.mul_apply,Fin.sum_univ_succ]
  ring
def homZero (i j : Fin 18) : HomData π i j where
  v := 0
  commutes := by intros; simp [equation,ambient,source,Matrix.mul_apply]
def homAdd {i j : Fin 18} (f g : HomData π i j) : HomData π i j where
  v := f.v+g.v
  commutes := by intros; rw [equation_add,f.commutes,g.commutes,add_zero]
def homScale {i j : Fin 18} (x : R) (f : HomData π i j) : HomData π i j where
  v := fun z => x*f.v z
  commutes := by intros; rw [equation_smul,f.commutes,mul_zero]
abbrev RawMatrix := ∀ i j, HomData π i j
def part (i : Fin 19) : Fin 3 := if i=18 then 1 else 0
def reduction (f : RawMatrix π) : Mat k := fun i j =>
  ρ ((f (slotVertex i) (slotVertex j)).v ⟨(part i).val*3+(part j).val,by have := (part i).isLt; have := (part j).isLt; omega⟩)
include h5 ann in
theorem reduction_supported (f : RawMatrix π) : Supported k (reduction π ρ f) := by
  intro i j hij
  fin_cases i
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact image_0_1_0 π ρ h5 ann (f 0 1)
    · exact image_0_2_0 π ρ h5 ann (f 0 2)
    · exact image_0_3_0 π ρ h5 ann (f 0 3)
    · exact image_0_4_0 π ρ h5 ann (f 0 4)
    · exact image_0_5_0 π ρ h5 ann (f 0 5)
    · exact image_0_6_0 π ρ h5 ann (f 0 6)
    · exact image_0_7_0 π ρ h5 ann (f 0 7)
    · exact image_0_8_0 π ρ h5 ann (f 0 8)
    · exact image_0_9_0 π ρ h5 ann (f 0 9)
    · exact image_0_10_0 π ρ h5 ann (f 0 10)
    · exact image_0_11_0 π ρ h5 ann (f 0 11)
    · exact image_0_12_0 π ρ h5 ann (f 0 12)
    · exact image_0_13_0 π ρ h5 ann (f 0 13)
    · exact image_0_14_0 π ρ h5 ann (f 0 14)
    · exact image_0_15_0 π ρ h5 ann (f 0 15)
    · exact image_0_16_0 π ρ h5 ann (f 0 16)
    · exact image_0_17_0 π ρ h5 ann (f 0 17)
    · exact image_0_17_1 π ρ h5 ann (f 0 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_1_2_0 π ρ h5 ann (f 1 2)
    · exact image_1_3_0 π ρ h5 ann (f 1 3)
    · exact image_1_4_0 π ρ h5 ann (f 1 4)
    · exact image_1_5_0 π ρ h5 ann (f 1 5)
    · exact image_1_6_0 π ρ h5 ann (f 1 6)
    · exact image_1_7_0 π ρ h5 ann (f 1 7)
    · exact image_1_8_0 π ρ h5 ann (f 1 8)
    · exact image_1_9_0 π ρ h5 ann (f 1 9)
    · exact image_1_10_0 π ρ h5 ann (f 1 10)
    · exact image_1_11_0 π ρ h5 ann (f 1 11)
    · exact image_1_12_0 π ρ h5 ann (f 1 12)
    · exact image_1_13_0 π ρ h5 ann (f 1 13)
    · exact image_1_14_0 π ρ h5 ann (f 1 14)
    · exact image_1_15_0 π ρ h5 ann (f 1 15)
    · exact image_1_16_0 π ρ h5 ann (f 1 16)
    · exact image_1_17_0 π ρ h5 ann (f 1 17)
    · exact image_1_17_1 π ρ h5 ann (f 1 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_2_3_0 π ρ h5 ann (f 2 3)
    · exact image_2_4_0 π ρ h5 ann (f 2 4)
    · exact image_2_5_0 π ρ h5 ann (f 2 5)
    · exact False.elim (hij (by decide))
    · exact image_2_7_0 π ρ h5 ann (f 2 7)
    · exact image_2_8_0 π ρ h5 ann (f 2 8)
    · exact False.elim (hij (by decide))
    · exact image_2_10_0 π ρ h5 ann (f 2 10)
    · exact image_2_11_0 π ρ h5 ann (f 2 11)
    · exact image_2_12_0 π ρ h5 ann (f 2 12)
    · exact False.elim (hij (by decide))
    · exact image_2_14_0 π ρ h5 ann (f 2 14)
    · exact image_2_15_0 π ρ h5 ann (f 2 15)
    · exact image_2_16_0 π ρ h5 ann (f 2 16)
    · exact False.elim (hij (by decide))
    · exact image_2_17_0 π ρ h5 ann (f 2 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_3_4_0 π ρ h5 ann (f 3 4)
    · exact image_3_5_0 π ρ h5 ann (f 3 5)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_3_8_0 π ρ h5 ann (f 3 8)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_3_12_0 π ρ h5 ann (f 3 12)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_3_15_0 π ρ h5 ann (f 3 15)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_3_17_0 π ρ h5 ann (f 3 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_4_5_0 π ρ h5 ann (f 4 5)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_6_2_0 π ρ h5 ann (f 6 2)
    · exact image_6_3_0 π ρ h5 ann (f 6 3)
    · exact image_6_4_0 π ρ h5 ann (f 6 4)
    · exact image_6_5_0 π ρ h5 ann (f 6 5)
    · exact False.elim (hij (by decide))
    · exact image_6_7_0 π ρ h5 ann (f 6 7)
    · exact image_6_8_0 π ρ h5 ann (f 6 8)
    · exact image_6_9_0 π ρ h5 ann (f 6 9)
    · exact image_6_10_0 π ρ h5 ann (f 6 10)
    · exact image_6_11_0 π ρ h5 ann (f 6 11)
    · exact image_6_12_0 π ρ h5 ann (f 6 12)
    · exact image_6_13_0 π ρ h5 ann (f 6 13)
    · exact image_6_14_0 π ρ h5 ann (f 6 14)
    · exact image_6_15_0 π ρ h5 ann (f 6 15)
    · exact image_6_16_0 π ρ h5 ann (f 6 16)
    · exact image_6_17_0 π ρ h5 ann (f 6 17)
    · exact image_6_17_1 π ρ h5 ann (f 6 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_7_3_0 π ρ h5 ann (f 7 3)
    · exact image_7_4_0 π ρ h5 ann (f 7 4)
    · exact image_7_5_0 π ρ h5 ann (f 7 5)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_7_8_0 π ρ h5 ann (f 7 8)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_7_11_0 π ρ h5 ann (f 7 11)
    · exact image_7_12_0 π ρ h5 ann (f 7 12)
    · exact False.elim (hij (by decide))
    · exact image_7_14_0 π ρ h5 ann (f 7 14)
    · exact image_7_15_0 π ρ h5 ann (f 7 15)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_7_17_0 π ρ h5 ann (f 7 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_8_4_0 π ρ h5 ann (f 8 4)
    · exact image_8_5_0 π ρ h5 ann (f 8 5)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_9_2_0 π ρ h5 ann (f 9 2)
    · exact image_9_3_0 π ρ h5 ann (f 9 3)
    · exact image_9_4_0 π ρ h5 ann (f 9 4)
    · exact image_9_5_0 π ρ h5 ann (f 9 5)
    · exact False.elim (hij (by decide))
    · exact image_9_7_0 π ρ h5 ann (f 9 7)
    · exact image_9_8_0 π ρ h5 ann (f 9 8)
    · exact False.elim (hij (by decide))
    · exact image_9_10_0 π ρ h5 ann (f 9 10)
    · exact image_9_11_0 π ρ h5 ann (f 9 11)
    · exact image_9_12_0 π ρ h5 ann (f 9 12)
    · exact image_9_13_0 π ρ h5 ann (f 9 13)
    · exact image_9_14_0 π ρ h5 ann (f 9 14)
    · exact image_9_15_0 π ρ h5 ann (f 9 15)
    · exact image_9_16_0 π ρ h5 ann (f 9 16)
    · exact image_9_17_0 π ρ h5 ann (f 9 17)
    · exact image_9_17_1 π ρ h5 ann (f 9 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_10_2_0 π ρ h5 ann (f 10 2)
    · exact image_10_3_0 π ρ h5 ann (f 10 3)
    · exact image_10_4_0 π ρ h5 ann (f 10 4)
    · exact image_10_5_0 π ρ h5 ann (f 10 5)
    · exact False.elim (hij (by decide))
    · exact image_10_7_0 π ρ h5 ann (f 10 7)
    · exact image_10_8_0 π ρ h5 ann (f 10 8)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_10_11_0 π ρ h5 ann (f 10 11)
    · exact image_10_12_0 π ρ h5 ann (f 10 12)
    · exact image_10_13_0 π ρ h5 ann (f 10 13)
    · exact image_10_14_0 π ρ h5 ann (f 10 14)
    · exact image_10_15_0 π ρ h5 ann (f 10 15)
    · exact image_10_16_0 π ρ h5 ann (f 10 16)
    · exact False.elim (hij (by decide))
    · exact image_10_17_0 π ρ h5 ann (f 10 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_11_3_0 π ρ h5 ann (f 11 3)
    · exact image_11_4_0 π ρ h5 ann (f 11 4)
    · exact image_11_5_0 π ρ h5 ann (f 11 5)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_11_8_0 π ρ h5 ann (f 11 8)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_11_12_0 π ρ h5 ann (f 11 12)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_11_15_0 π ρ h5 ann (f 11 15)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_11_17_0 π ρ h5 ann (f 11 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_12_3_0 π ρ h5 ann (f 12 3)
    · exact image_12_4_0 π ρ h5 ann (f 12 4)
    · exact image_12_5_0 π ρ h5 ann (f 12 5)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_12_8_0 π ρ h5 ann (f 12 8)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_12_17_0 π ρ h5 ann (f 12 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_13_2_0 π ρ h5 ann (f 13 2)
    · exact image_13_3_0 π ρ h5 ann (f 13 3)
    · exact image_13_4_0 π ρ h5 ann (f 13 4)
    · exact image_13_5_0 π ρ h5 ann (f 13 5)
    · exact False.elim (hij (by decide))
    · exact image_13_7_0 π ρ h5 ann (f 13 7)
    · exact image_13_8_0 π ρ h5 ann (f 13 8)
    · exact False.elim (hij (by decide))
    · exact image_13_10_0 π ρ h5 ann (f 13 10)
    · exact image_13_11_0 π ρ h5 ann (f 13 11)
    · exact image_13_12_0 π ρ h5 ann (f 13 12)
    · exact False.elim (hij (by decide))
    · exact image_13_14_0 π ρ h5 ann (f 13 14)
    · exact image_13_15_0 π ρ h5 ann (f 13 15)
    · exact image_13_16_0 π ρ h5 ann (f 13 16)
    · exact False.elim (hij (by decide))
    · exact image_13_17_0 π ρ h5 ann (f 13 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_14_2_0 π ρ h5 ann (f 14 2)
    · exact image_14_3_0 π ρ h5 ann (f 14 3)
    · exact image_14_4_0 π ρ h5 ann (f 14 4)
    · exact image_14_5_0 π ρ h5 ann (f 14 5)
    · exact False.elim (hij (by decide))
    · exact image_14_7_0 π ρ h5 ann (f 14 7)
    · exact image_14_8_0 π ρ h5 ann (f 14 8)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_14_11_0 π ρ h5 ann (f 14 11)
    · exact image_14_12_0 π ρ h5 ann (f 14 12)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_14_15_0 π ρ h5 ann (f 14 15)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_14_17_0 π ρ h5 ann (f 14 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_15_2_0 π ρ h5 ann (f 15 2)
    · exact image_15_3_0 π ρ h5 ann (f 15 3)
    · exact image_15_4_0 π ρ h5 ann (f 15 4)
    · exact image_15_5_0 π ρ h5 ann (f 15 5)
    · exact False.elim (hij (by decide))
    · exact image_15_7_0 π ρ h5 ann (f 15 7)
    · exact image_15_8_0 π ρ h5 ann (f 15 8)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_15_11_0 π ρ h5 ann (f 15 11)
    · exact image_15_12_0 π ρ h5 ann (f 15 12)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_15_17_0 π ρ h5 ann (f 15 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_16_2_0 π ρ h5 ann (f 16 2)
    · exact image_16_3_0 π ρ h5 ann (f 16 3)
    · exact image_16_4_0 π ρ h5 ann (f 16 4)
    · exact image_16_5_0 π ρ h5 ann (f 16 5)
    · exact False.elim (hij (by decide))
    · exact image_16_7_0 π ρ h5 ann (f 16 7)
    · exact image_16_8_0 π ρ h5 ann (f 16 8)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_16_11_0 π ρ h5 ann (f 16 11)
    · exact image_16_12_0 π ρ h5 ann (f 16 12)
    · exact False.elim (hij (by decide))
    · exact image_16_14_0 π ρ h5 ann (f 16 14)
    · exact image_16_15_0 π ρ h5 ann (f 16 15)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_16_17_0 π ρ h5 ann (f 16 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_17_2_0 π ρ h5 ann (f 17 2)
    · exact image_17_3_0 π ρ h5 ann (f 17 3)
    · exact image_17_4_0 π ρ h5 ann (f 17 4)
    · exact image_17_5_0 π ρ h5 ann (f 17 5)
    · exact False.elim (hij (by decide))
    · exact image_17_7_0 π ρ h5 ann (f 17 7)
    · exact image_17_8_0 π ρ h5 ann (f 17 8)
    · exact False.elim (hij (by decide))
    · exact image_17_10_0 π ρ h5 ann (f 17 10)
    · exact image_17_11_0 π ρ h5 ann (f 17 11)
    · exact image_17_12_0 π ρ h5 ann (f 17 12)
    · exact image_17_13_0 π ρ h5 ann (f 17 13)
    · exact image_17_14_0 π ρ h5 ann (f 17 14)
    · exact image_17_15_0 π ρ h5 ann (f 17 15)
    · exact image_17_16_0 π ρ h5 ann (f 17 16)
    · exact False.elim (hij (by decide))
    · exact image_17_17_0 π ρ h5 ann (f 17 17)
  · fin_cases j
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_17_4_1 π ρ h5 ann (f 17 4)
    · exact image_17_5_1 π ρ h5 ann (f 17 5)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact image_17_8_1 π ρ h5 ann (f 17 8)
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
    · exact False.elim (hij (by decide))
include h5 ann in
def reduce (f : RawMatrix π) : End k := ⟨reduction π ρ f,reduction_supported π ρ h5 ann f,by
  have h := image_17_17_1 π ρ h5 ann (f 17 17)
  simp only [map_add,map_neg,neg_add_eq_zero] at h
  exact h⟩
include h5 in
def liftValues (c : Mat R) (i j : Fin 18) : HomData π i j :=
  match i,j with
  | ⟨0,_⟩,⟨0,_⟩ => homScale π (c 0 0) (lift_0_0_0 π h5)
  | ⟨0,_⟩,⟨1,_⟩ => homZero π 0 1
  | ⟨0,_⟩,⟨2,_⟩ => homZero π 0 2
  | ⟨0,_⟩,⟨3,_⟩ => homZero π 0 3
  | ⟨0,_⟩,⟨4,_⟩ => homZero π 0 4
  | ⟨0,_⟩,⟨5,_⟩ => homZero π 0 5
  | ⟨0,_⟩,⟨6,_⟩ => homZero π 0 6
  | ⟨0,_⟩,⟨7,_⟩ => homZero π 0 7
  | ⟨0,_⟩,⟨8,_⟩ => homZero π 0 8
  | ⟨0,_⟩,⟨9,_⟩ => homZero π 0 9
  | ⟨0,_⟩,⟨10,_⟩ => homZero π 0 10
  | ⟨0,_⟩,⟨11,_⟩ => homZero π 0 11
  | ⟨0,_⟩,⟨12,_⟩ => homZero π 0 12
  | ⟨0,_⟩,⟨13,_⟩ => homZero π 0 13
  | ⟨0,_⟩,⟨14,_⟩ => homZero π 0 14
  | ⟨0,_⟩,⟨15,_⟩ => homZero π 0 15
  | ⟨0,_⟩,⟨16,_⟩ => homZero π 0 16
  | ⟨0,_⟩,⟨17,_⟩ => homZero π 0 17
  | ⟨1,_⟩,⟨0,_⟩ => homScale π (c 1 0) (lift_1_0_0 π h5)
  | ⟨1,_⟩,⟨1,_⟩ => homScale π (c 1 1) (lift_1_1_0 π h5)
  | ⟨1,_⟩,⟨2,_⟩ => homZero π 1 2
  | ⟨1,_⟩,⟨3,_⟩ => homZero π 1 3
  | ⟨1,_⟩,⟨4,_⟩ => homZero π 1 4
  | ⟨1,_⟩,⟨5,_⟩ => homZero π 1 5
  | ⟨1,_⟩,⟨6,_⟩ => homZero π 1 6
  | ⟨1,_⟩,⟨7,_⟩ => homZero π 1 7
  | ⟨1,_⟩,⟨8,_⟩ => homZero π 1 8
  | ⟨1,_⟩,⟨9,_⟩ => homZero π 1 9
  | ⟨1,_⟩,⟨10,_⟩ => homZero π 1 10
  | ⟨1,_⟩,⟨11,_⟩ => homZero π 1 11
  | ⟨1,_⟩,⟨12,_⟩ => homZero π 1 12
  | ⟨1,_⟩,⟨13,_⟩ => homZero π 1 13
  | ⟨1,_⟩,⟨14,_⟩ => homZero π 1 14
  | ⟨1,_⟩,⟨15,_⟩ => homZero π 1 15
  | ⟨1,_⟩,⟨16,_⟩ => homZero π 1 16
  | ⟨1,_⟩,⟨17,_⟩ => homZero π 1 17
  | ⟨2,_⟩,⟨0,_⟩ => homScale π (c 2 0) (lift_2_0_0 π h5)
  | ⟨2,_⟩,⟨1,_⟩ => homScale π (c 2 1) (lift_2_1_0 π h5)
  | ⟨2,_⟩,⟨2,_⟩ => homScale π (c 2 2) (lift_2_2_0 π h5)
  | ⟨2,_⟩,⟨3,_⟩ => homZero π 2 3
  | ⟨2,_⟩,⟨4,_⟩ => homZero π 2 4
  | ⟨2,_⟩,⟨5,_⟩ => homZero π 2 5
  | ⟨2,_⟩,⟨6,_⟩ => homScale π (c 2 6) (lift_2_6_0 π h5)
  | ⟨2,_⟩,⟨7,_⟩ => homZero π 2 7
  | ⟨2,_⟩,⟨8,_⟩ => homZero π 2 8
  | ⟨2,_⟩,⟨9,_⟩ => homScale π (c 2 9) (lift_2_9_0 π h5)
  | ⟨2,_⟩,⟨10,_⟩ => homZero π 2 10
  | ⟨2,_⟩,⟨11,_⟩ => homZero π 2 11
  | ⟨2,_⟩,⟨12,_⟩ => homZero π 2 12
  | ⟨2,_⟩,⟨13,_⟩ => homScale π (c 2 13) (lift_2_13_0 π h5)
  | ⟨2,_⟩,⟨14,_⟩ => homZero π 2 14
  | ⟨2,_⟩,⟨15,_⟩ => homZero π 2 15
  | ⟨2,_⟩,⟨16,_⟩ => homZero π 2 16
  | ⟨2,_⟩,⟨17,_⟩ => homScale π (c 2 17) (lift_2_17_0 π h5)
  | ⟨3,_⟩,⟨0,_⟩ => homScale π (c 3 0) (lift_3_0_0 π h5)
  | ⟨3,_⟩,⟨1,_⟩ => homScale π (c 3 1) (lift_3_1_0 π h5)
  | ⟨3,_⟩,⟨2,_⟩ => homScale π (c 3 2) (lift_3_2_0 π h5)
  | ⟨3,_⟩,⟨3,_⟩ => homScale π (c 3 3) (lift_3_3_0 π h5)
  | ⟨3,_⟩,⟨4,_⟩ => homZero π 3 4
  | ⟨3,_⟩,⟨5,_⟩ => homZero π 3 5
  | ⟨3,_⟩,⟨6,_⟩ => homScale π (c 3 6) (lift_3_6_0 π h5)
  | ⟨3,_⟩,⟨7,_⟩ => homScale π (c 3 7) (lift_3_7_0 π h5)
  | ⟨3,_⟩,⟨8,_⟩ => homZero π 3 8
  | ⟨3,_⟩,⟨9,_⟩ => homScale π (c 3 9) (lift_3_9_0 π h5)
  | ⟨3,_⟩,⟨10,_⟩ => homScale π (c 3 10) (lift_3_10_0 π h5)
  | ⟨3,_⟩,⟨11,_⟩ => homScale π (c 3 11) (lift_3_11_0 π h5)
  | ⟨3,_⟩,⟨12,_⟩ => homZero π 3 12
  | ⟨3,_⟩,⟨13,_⟩ => homScale π (c 3 13) (lift_3_13_0 π h5)
  | ⟨3,_⟩,⟨14,_⟩ => homScale π (c 3 14) (lift_3_14_0 π h5)
  | ⟨3,_⟩,⟨15,_⟩ => homZero π 3 15
  | ⟨3,_⟩,⟨16,_⟩ => homScale π (c 3 16) (lift_3_16_0 π h5)
  | ⟨3,_⟩,⟨17,_⟩ => homScale π (c 3 17) (lift_3_17_0 π h5)
  | ⟨4,_⟩,⟨0,_⟩ => homScale π (c 4 0) (lift_4_0_0 π h5)
  | ⟨4,_⟩,⟨1,_⟩ => homScale π (c 4 1) (lift_4_1_0 π h5)
  | ⟨4,_⟩,⟨2,_⟩ => homScale π (c 4 2) (lift_4_2_0 π h5)
  | ⟨4,_⟩,⟨3,_⟩ => homScale π (c 4 3) (lift_4_3_0 π h5)
  | ⟨4,_⟩,⟨4,_⟩ => homScale π (c 4 4) (lift_4_4_0 π h5)
  | ⟨4,_⟩,⟨5,_⟩ => homZero π 4 5
  | ⟨4,_⟩,⟨6,_⟩ => homScale π (c 4 6) (lift_4_6_0 π h5)
  | ⟨4,_⟩,⟨7,_⟩ => homScale π (c 4 7) (lift_4_7_0 π h5)
  | ⟨4,_⟩,⟨8,_⟩ => homScale π (c 4 8) (lift_4_8_0 π h5)
  | ⟨4,_⟩,⟨9,_⟩ => homScale π (c 4 9) (lift_4_9_0 π h5)
  | ⟨4,_⟩,⟨10,_⟩ => homScale π (c 4 10) (lift_4_10_0 π h5)
  | ⟨4,_⟩,⟨11,_⟩ => homScale π (c 4 11) (lift_4_11_0 π h5)
  | ⟨4,_⟩,⟨12,_⟩ => homScale π (c 4 12) (lift_4_12_0 π h5)
  | ⟨4,_⟩,⟨13,_⟩ => homScale π (c 4 13) (lift_4_13_0 π h5)
  | ⟨4,_⟩,⟨14,_⟩ => homScale π (c 4 14) (lift_4_14_0 π h5)
  | ⟨4,_⟩,⟨15,_⟩ => homScale π (c 4 15) (lift_4_15_0 π h5)
  | ⟨4,_⟩,⟨16,_⟩ => homScale π (c 4 16) (lift_4_16_0 π h5)
  | ⟨4,_⟩,⟨17,_⟩ => homAdd π (homScale π (c 4 17) (lift_4_17_0 π h5)) (homScale π (c 4 18) (lift_4_17_1 π h5))
  | ⟨5,_⟩,⟨0,_⟩ => homScale π (c 5 0) (lift_5_0_0 π h5)
  | ⟨5,_⟩,⟨1,_⟩ => homScale π (c 5 1) (lift_5_1_0 π h5)
  | ⟨5,_⟩,⟨2,_⟩ => homScale π (c 5 2) (lift_5_2_0 π h5)
  | ⟨5,_⟩,⟨3,_⟩ => homScale π (c 5 3) (lift_5_3_0 π h5)
  | ⟨5,_⟩,⟨4,_⟩ => homScale π (c 5 4) (lift_5_4_0 π h5)
  | ⟨5,_⟩,⟨5,_⟩ => homScale π (c 5 5) (lift_5_5_0 π h5)
  | ⟨5,_⟩,⟨6,_⟩ => homScale π (c 5 6) (lift_5_6_0 π h5)
  | ⟨5,_⟩,⟨7,_⟩ => homScale π (c 5 7) (lift_5_7_0 π h5)
  | ⟨5,_⟩,⟨8,_⟩ => homScale π (c 5 8) (lift_5_8_0 π h5)
  | ⟨5,_⟩,⟨9,_⟩ => homScale π (c 5 9) (lift_5_9_0 π h5)
  | ⟨5,_⟩,⟨10,_⟩ => homScale π (c 5 10) (lift_5_10_0 π h5)
  | ⟨5,_⟩,⟨11,_⟩ => homScale π (c 5 11) (lift_5_11_0 π h5)
  | ⟨5,_⟩,⟨12,_⟩ => homScale π (c 5 12) (lift_5_12_0 π h5)
  | ⟨5,_⟩,⟨13,_⟩ => homScale π (c 5 13) (lift_5_13_0 π h5)
  | ⟨5,_⟩,⟨14,_⟩ => homScale π (c 5 14) (lift_5_14_0 π h5)
  | ⟨5,_⟩,⟨15,_⟩ => homScale π (c 5 15) (lift_5_15_0 π h5)
  | ⟨5,_⟩,⟨16,_⟩ => homScale π (c 5 16) (lift_5_16_0 π h5)
  | ⟨5,_⟩,⟨17,_⟩ => homAdd π (homScale π (c 5 17) (lift_5_17_0 π h5)) (homScale π (c 5 18) (lift_5_17_1 π h5))
  | ⟨6,_⟩,⟨0,_⟩ => homScale π (c 6 0) (lift_6_0_0 π h5)
  | ⟨6,_⟩,⟨1,_⟩ => homScale π (c 6 1) (lift_6_1_0 π h5)
  | ⟨6,_⟩,⟨2,_⟩ => homZero π 6 2
  | ⟨6,_⟩,⟨3,_⟩ => homZero π 6 3
  | ⟨6,_⟩,⟨4,_⟩ => homZero π 6 4
  | ⟨6,_⟩,⟨5,_⟩ => homZero π 6 5
  | ⟨6,_⟩,⟨6,_⟩ => homScale π (c 6 6) (lift_6_6_0 π h5)
  | ⟨6,_⟩,⟨7,_⟩ => homZero π 6 7
  | ⟨6,_⟩,⟨8,_⟩ => homZero π 6 8
  | ⟨6,_⟩,⟨9,_⟩ => homZero π 6 9
  | ⟨6,_⟩,⟨10,_⟩ => homZero π 6 10
  | ⟨6,_⟩,⟨11,_⟩ => homZero π 6 11
  | ⟨6,_⟩,⟨12,_⟩ => homZero π 6 12
  | ⟨6,_⟩,⟨13,_⟩ => homZero π 6 13
  | ⟨6,_⟩,⟨14,_⟩ => homZero π 6 14
  | ⟨6,_⟩,⟨15,_⟩ => homZero π 6 15
  | ⟨6,_⟩,⟨16,_⟩ => homZero π 6 16
  | ⟨6,_⟩,⟨17,_⟩ => homZero π 6 17
  | ⟨7,_⟩,⟨0,_⟩ => homScale π (c 7 0) (lift_7_0_0 π h5)
  | ⟨7,_⟩,⟨1,_⟩ => homScale π (c 7 1) (lift_7_1_0 π h5)
  | ⟨7,_⟩,⟨2,_⟩ => homScale π (c 7 2) (lift_7_2_0 π h5)
  | ⟨7,_⟩,⟨3,_⟩ => homZero π 7 3
  | ⟨7,_⟩,⟨4,_⟩ => homZero π 7 4
  | ⟨7,_⟩,⟨5,_⟩ => homZero π 7 5
  | ⟨7,_⟩,⟨6,_⟩ => homScale π (c 7 6) (lift_7_6_0 π h5)
  | ⟨7,_⟩,⟨7,_⟩ => homScale π (c 7 7) (lift_7_7_0 π h5)
  | ⟨7,_⟩,⟨8,_⟩ => homZero π 7 8
  | ⟨7,_⟩,⟨9,_⟩ => homScale π (c 7 9) (lift_7_9_0 π h5)
  | ⟨7,_⟩,⟨10,_⟩ => homScale π (c 7 10) (lift_7_10_0 π h5)
  | ⟨7,_⟩,⟨11,_⟩ => homZero π 7 11
  | ⟨7,_⟩,⟨12,_⟩ => homZero π 7 12
  | ⟨7,_⟩,⟨13,_⟩ => homScale π (c 7 13) (lift_7_13_0 π h5)
  | ⟨7,_⟩,⟨14,_⟩ => homZero π 7 14
  | ⟨7,_⟩,⟨15,_⟩ => homZero π 7 15
  | ⟨7,_⟩,⟨16,_⟩ => homScale π (c 7 16) (lift_7_16_0 π h5)
  | ⟨7,_⟩,⟨17,_⟩ => homScale π (c 7 17) (lift_7_17_0 π h5)
  | ⟨8,_⟩,⟨0,_⟩ => homScale π (c 8 0) (lift_8_0_0 π h5)
  | ⟨8,_⟩,⟨1,_⟩ => homScale π (c 8 1) (lift_8_1_0 π h5)
  | ⟨8,_⟩,⟨2,_⟩ => homScale π (c 8 2) (lift_8_2_0 π h5)
  | ⟨8,_⟩,⟨3,_⟩ => homScale π (c 8 3) (lift_8_3_0 π h5)
  | ⟨8,_⟩,⟨4,_⟩ => homZero π 8 4
  | ⟨8,_⟩,⟨5,_⟩ => homZero π 8 5
  | ⟨8,_⟩,⟨6,_⟩ => homScale π (c 8 6) (lift_8_6_0 π h5)
  | ⟨8,_⟩,⟨7,_⟩ => homScale π (c 8 7) (lift_8_7_0 π h5)
  | ⟨8,_⟩,⟨8,_⟩ => homScale π (c 8 8) (lift_8_8_0 π h5)
  | ⟨8,_⟩,⟨9,_⟩ => homScale π (c 8 9) (lift_8_9_0 π h5)
  | ⟨8,_⟩,⟨10,_⟩ => homScale π (c 8 10) (lift_8_10_0 π h5)
  | ⟨8,_⟩,⟨11,_⟩ => homScale π (c 8 11) (lift_8_11_0 π h5)
  | ⟨8,_⟩,⟨12,_⟩ => homScale π (c 8 12) (lift_8_12_0 π h5)
  | ⟨8,_⟩,⟨13,_⟩ => homScale π (c 8 13) (lift_8_13_0 π h5)
  | ⟨8,_⟩,⟨14,_⟩ => homScale π (c 8 14) (lift_8_14_0 π h5)
  | ⟨8,_⟩,⟨15,_⟩ => homScale π (c 8 15) (lift_8_15_0 π h5)
  | ⟨8,_⟩,⟨16,_⟩ => homScale π (c 8 16) (lift_8_16_0 π h5)
  | ⟨8,_⟩,⟨17,_⟩ => homAdd π (homScale π (c 8 17) (lift_8_17_0 π h5)) (homScale π (c 8 18) (lift_8_17_1 π h5))
  | ⟨9,_⟩,⟨0,_⟩ => homScale π (c 9 0) (lift_9_0_0 π h5)
  | ⟨9,_⟩,⟨1,_⟩ => homScale π (c 9 1) (lift_9_1_0 π h5)
  | ⟨9,_⟩,⟨2,_⟩ => homZero π 9 2
  | ⟨9,_⟩,⟨3,_⟩ => homZero π 9 3
  | ⟨9,_⟩,⟨4,_⟩ => homZero π 9 4
  | ⟨9,_⟩,⟨5,_⟩ => homZero π 9 5
  | ⟨9,_⟩,⟨6,_⟩ => homScale π (c 9 6) (lift_9_6_0 π h5)
  | ⟨9,_⟩,⟨7,_⟩ => homZero π 9 7
  | ⟨9,_⟩,⟨8,_⟩ => homZero π 9 8
  | ⟨9,_⟩,⟨9,_⟩ => homScale π (c 9 9) (lift_9_9_0 π h5)
  | ⟨9,_⟩,⟨10,_⟩ => homZero π 9 10
  | ⟨9,_⟩,⟨11,_⟩ => homZero π 9 11
  | ⟨9,_⟩,⟨12,_⟩ => homZero π 9 12
  | ⟨9,_⟩,⟨13,_⟩ => homZero π 9 13
  | ⟨9,_⟩,⟨14,_⟩ => homZero π 9 14
  | ⟨9,_⟩,⟨15,_⟩ => homZero π 9 15
  | ⟨9,_⟩,⟨16,_⟩ => homZero π 9 16
  | ⟨9,_⟩,⟨17,_⟩ => homZero π 9 17
  | ⟨10,_⟩,⟨0,_⟩ => homScale π (c 10 0) (lift_10_0_0 π h5)
  | ⟨10,_⟩,⟨1,_⟩ => homScale π (c 10 1) (lift_10_1_0 π h5)
  | ⟨10,_⟩,⟨2,_⟩ => homZero π 10 2
  | ⟨10,_⟩,⟨3,_⟩ => homZero π 10 3
  | ⟨10,_⟩,⟨4,_⟩ => homZero π 10 4
  | ⟨10,_⟩,⟨5,_⟩ => homZero π 10 5
  | ⟨10,_⟩,⟨6,_⟩ => homScale π (c 10 6) (lift_10_6_0 π h5)
  | ⟨10,_⟩,⟨7,_⟩ => homZero π 10 7
  | ⟨10,_⟩,⟨8,_⟩ => homZero π 10 8
  | ⟨10,_⟩,⟨9,_⟩ => homScale π (c 10 9) (lift_10_9_0 π h5)
  | ⟨10,_⟩,⟨10,_⟩ => homScale π (c 10 10) (lift_10_10_0 π h5)
  | ⟨10,_⟩,⟨11,_⟩ => homZero π 10 11
  | ⟨10,_⟩,⟨12,_⟩ => homZero π 10 12
  | ⟨10,_⟩,⟨13,_⟩ => homZero π 10 13
  | ⟨10,_⟩,⟨14,_⟩ => homZero π 10 14
  | ⟨10,_⟩,⟨15,_⟩ => homZero π 10 15
  | ⟨10,_⟩,⟨16,_⟩ => homZero π 10 16
  | ⟨10,_⟩,⟨17,_⟩ => homScale π (c 10 17) (lift_10_17_0 π h5)
  | ⟨11,_⟩,⟨0,_⟩ => homScale π (c 11 0) (lift_11_0_0 π h5)
  | ⟨11,_⟩,⟨1,_⟩ => homScale π (c 11 1) (lift_11_1_0 π h5)
  | ⟨11,_⟩,⟨2,_⟩ => homScale π (c 11 2) (lift_11_2_0 π h5)
  | ⟨11,_⟩,⟨3,_⟩ => homZero π 11 3
  | ⟨11,_⟩,⟨4,_⟩ => homZero π 11 4
  | ⟨11,_⟩,⟨5,_⟩ => homZero π 11 5
  | ⟨11,_⟩,⟨6,_⟩ => homScale π (c 11 6) (lift_11_6_0 π h5)
  | ⟨11,_⟩,⟨7,_⟩ => homScale π (c 11 7) (lift_11_7_0 π h5)
  | ⟨11,_⟩,⟨8,_⟩ => homZero π 11 8
  | ⟨11,_⟩,⟨9,_⟩ => homScale π (c 11 9) (lift_11_9_0 π h5)
  | ⟨11,_⟩,⟨10,_⟩ => homScale π (c 11 10) (lift_11_10_0 π h5)
  | ⟨11,_⟩,⟨11,_⟩ => homScale π (c 11 11) (lift_11_11_0 π h5)
  | ⟨11,_⟩,⟨12,_⟩ => homZero π 11 12
  | ⟨11,_⟩,⟨13,_⟩ => homScale π (c 11 13) (lift_11_13_0 π h5)
  | ⟨11,_⟩,⟨14,_⟩ => homScale π (c 11 14) (lift_11_14_0 π h5)
  | ⟨11,_⟩,⟨15,_⟩ => homZero π 11 15
  | ⟨11,_⟩,⟨16,_⟩ => homScale π (c 11 16) (lift_11_16_0 π h5)
  | ⟨11,_⟩,⟨17,_⟩ => homScale π (c 11 17) (lift_11_17_0 π h5)
  | ⟨12,_⟩,⟨0,_⟩ => homScale π (c 12 0) (lift_12_0_0 π h5)
  | ⟨12,_⟩,⟨1,_⟩ => homScale π (c 12 1) (lift_12_1_0 π h5)
  | ⟨12,_⟩,⟨2,_⟩ => homScale π (c 12 2) (lift_12_2_0 π h5)
  | ⟨12,_⟩,⟨3,_⟩ => homZero π 12 3
  | ⟨12,_⟩,⟨4,_⟩ => homZero π 12 4
  | ⟨12,_⟩,⟨5,_⟩ => homZero π 12 5
  | ⟨12,_⟩,⟨6,_⟩ => homScale π (c 12 6) (lift_12_6_0 π h5)
  | ⟨12,_⟩,⟨7,_⟩ => homScale π (c 12 7) (lift_12_7_0 π h5)
  | ⟨12,_⟩,⟨8,_⟩ => homZero π 12 8
  | ⟨12,_⟩,⟨9,_⟩ => homScale π (c 12 9) (lift_12_9_0 π h5)
  | ⟨12,_⟩,⟨10,_⟩ => homScale π (c 12 10) (lift_12_10_0 π h5)
  | ⟨12,_⟩,⟨11,_⟩ => homScale π (c 12 11) (lift_12_11_0 π h5)
  | ⟨12,_⟩,⟨12,_⟩ => homScale π (c 12 12) (lift_12_12_0 π h5)
  | ⟨12,_⟩,⟨13,_⟩ => homScale π (c 12 13) (lift_12_13_0 π h5)
  | ⟨12,_⟩,⟨14,_⟩ => homScale π (c 12 14) (lift_12_14_0 π h5)
  | ⟨12,_⟩,⟨15,_⟩ => homScale π (c 12 15) (lift_12_15_0 π h5)
  | ⟨12,_⟩,⟨16,_⟩ => homScale π (c 12 16) (lift_12_16_0 π h5)
  | ⟨12,_⟩,⟨17,_⟩ => homScale π (c 12 17) (lift_12_17_0 π h5)
  | ⟨13,_⟩,⟨0,_⟩ => homScale π (c 13 0) (lift_13_0_0 π h5)
  | ⟨13,_⟩,⟨1,_⟩ => homScale π (c 13 1) (lift_13_1_0 π h5)
  | ⟨13,_⟩,⟨2,_⟩ => homZero π 13 2
  | ⟨13,_⟩,⟨3,_⟩ => homZero π 13 3
  | ⟨13,_⟩,⟨4,_⟩ => homZero π 13 4
  | ⟨13,_⟩,⟨5,_⟩ => homZero π 13 5
  | ⟨13,_⟩,⟨6,_⟩ => homScale π (c 13 6) (lift_13_6_0 π h5)
  | ⟨13,_⟩,⟨7,_⟩ => homZero π 13 7
  | ⟨13,_⟩,⟨8,_⟩ => homZero π 13 8
  | ⟨13,_⟩,⟨9,_⟩ => homScale π (c 13 9) (lift_13_9_0 π h5)
  | ⟨13,_⟩,⟨10,_⟩ => homZero π 13 10
  | ⟨13,_⟩,⟨11,_⟩ => homZero π 13 11
  | ⟨13,_⟩,⟨12,_⟩ => homZero π 13 12
  | ⟨13,_⟩,⟨13,_⟩ => homScale π (c 13 13) (lift_13_13_0 π h5)
  | ⟨13,_⟩,⟨14,_⟩ => homZero π 13 14
  | ⟨13,_⟩,⟨15,_⟩ => homZero π 13 15
  | ⟨13,_⟩,⟨16,_⟩ => homZero π 13 16
  | ⟨13,_⟩,⟨17,_⟩ => homScale π (c 13 17) (lift_13_17_0 π h5)
  | ⟨14,_⟩,⟨0,_⟩ => homScale π (c 14 0) (lift_14_0_0 π h5)
  | ⟨14,_⟩,⟨1,_⟩ => homScale π (c 14 1) (lift_14_1_0 π h5)
  | ⟨14,_⟩,⟨2,_⟩ => homZero π 14 2
  | ⟨14,_⟩,⟨3,_⟩ => homZero π 14 3
  | ⟨14,_⟩,⟨4,_⟩ => homZero π 14 4
  | ⟨14,_⟩,⟨5,_⟩ => homZero π 14 5
  | ⟨14,_⟩,⟨6,_⟩ => homScale π (c 14 6) (lift_14_6_0 π h5)
  | ⟨14,_⟩,⟨7,_⟩ => homZero π 14 7
  | ⟨14,_⟩,⟨8,_⟩ => homZero π 14 8
  | ⟨14,_⟩,⟨9,_⟩ => homScale π (c 14 9) (lift_14_9_0 π h5)
  | ⟨14,_⟩,⟨10,_⟩ => homScale π (c 14 10) (lift_14_10_0 π h5)
  | ⟨14,_⟩,⟨11,_⟩ => homZero π 14 11
  | ⟨14,_⟩,⟨12,_⟩ => homZero π 14 12
  | ⟨14,_⟩,⟨13,_⟩ => homScale π (c 14 13) (lift_14_13_0 π h5)
  | ⟨14,_⟩,⟨14,_⟩ => homScale π (c 14 14) (lift_14_14_0 π h5)
  | ⟨14,_⟩,⟨15,_⟩ => homZero π 14 15
  | ⟨14,_⟩,⟨16,_⟩ => homScale π (c 14 16) (lift_14_16_0 π h5)
  | ⟨14,_⟩,⟨17,_⟩ => homScale π (c 14 17) (lift_14_17_0 π h5)
  | ⟨15,_⟩,⟨0,_⟩ => homScale π (c 15 0) (lift_15_0_0 π h5)
  | ⟨15,_⟩,⟨1,_⟩ => homScale π (c 15 1) (lift_15_1_0 π h5)
  | ⟨15,_⟩,⟨2,_⟩ => homZero π 15 2
  | ⟨15,_⟩,⟨3,_⟩ => homZero π 15 3
  | ⟨15,_⟩,⟨4,_⟩ => homZero π 15 4
  | ⟨15,_⟩,⟨5,_⟩ => homZero π 15 5
  | ⟨15,_⟩,⟨6,_⟩ => homScale π (c 15 6) (lift_15_6_0 π h5)
  | ⟨15,_⟩,⟨7,_⟩ => homZero π 15 7
  | ⟨15,_⟩,⟨8,_⟩ => homZero π 15 8
  | ⟨15,_⟩,⟨9,_⟩ => homScale π (c 15 9) (lift_15_9_0 π h5)
  | ⟨15,_⟩,⟨10,_⟩ => homScale π (c 15 10) (lift_15_10_0 π h5)
  | ⟨15,_⟩,⟨11,_⟩ => homZero π 15 11
  | ⟨15,_⟩,⟨12,_⟩ => homZero π 15 12
  | ⟨15,_⟩,⟨13,_⟩ => homScale π (c 15 13) (lift_15_13_0 π h5)
  | ⟨15,_⟩,⟨14,_⟩ => homScale π (c 15 14) (lift_15_14_0 π h5)
  | ⟨15,_⟩,⟨15,_⟩ => homScale π (c 15 15) (lift_15_15_0 π h5)
  | ⟨15,_⟩,⟨16,_⟩ => homScale π (c 15 16) (lift_15_16_0 π h5)
  | ⟨15,_⟩,⟨17,_⟩ => homScale π (c 15 17) (lift_15_17_0 π h5)
  | ⟨16,_⟩,⟨0,_⟩ => homScale π (c 16 0) (lift_16_0_0 π h5)
  | ⟨16,_⟩,⟨1,_⟩ => homScale π (c 16 1) (lift_16_1_0 π h5)
  | ⟨16,_⟩,⟨2,_⟩ => homZero π 16 2
  | ⟨16,_⟩,⟨3,_⟩ => homZero π 16 3
  | ⟨16,_⟩,⟨4,_⟩ => homZero π 16 4
  | ⟨16,_⟩,⟨5,_⟩ => homZero π 16 5
  | ⟨16,_⟩,⟨6,_⟩ => homScale π (c 16 6) (lift_16_6_0 π h5)
  | ⟨16,_⟩,⟨7,_⟩ => homZero π 16 7
  | ⟨16,_⟩,⟨8,_⟩ => homZero π 16 8
  | ⟨16,_⟩,⟨9,_⟩ => homScale π (c 16 9) (lift_16_9_0 π h5)
  | ⟨16,_⟩,⟨10,_⟩ => homScale π (c 16 10) (lift_16_10_0 π h5)
  | ⟨16,_⟩,⟨11,_⟩ => homZero π 16 11
  | ⟨16,_⟩,⟨12,_⟩ => homZero π 16 12
  | ⟨16,_⟩,⟨13,_⟩ => homScale π (c 16 13) (lift_16_13_0 π h5)
  | ⟨16,_⟩,⟨14,_⟩ => homZero π 16 14
  | ⟨16,_⟩,⟨15,_⟩ => homZero π 16 15
  | ⟨16,_⟩,⟨16,_⟩ => homScale π (c 16 16) (lift_16_16_0 π h5)
  | ⟨16,_⟩,⟨17,_⟩ => homScale π (c 16 17) (lift_16_17_0 π h5)
  | ⟨17,_⟩,⟨0,_⟩ => homAdd π (homScale π (c 17 0) (lift_17_0_0 π h5)) (homScale π (c 18 0) (lift_17_0_1 π h5))
  | ⟨17,_⟩,⟨1,_⟩ => homAdd π (homScale π (c 17 1) (lift_17_1_0 π h5)) (homScale π (c 18 1) (lift_17_1_1 π h5))
  | ⟨17,_⟩,⟨2,_⟩ => homScale π (c 18 2) (lift_17_2_0 π h5)
  | ⟨17,_⟩,⟨3,_⟩ => homScale π (c 18 3) (lift_17_3_0 π h5)
  | ⟨17,_⟩,⟨4,_⟩ => homZero π 17 4
  | ⟨17,_⟩,⟨5,_⟩ => homZero π 17 5
  | ⟨17,_⟩,⟨6,_⟩ => homAdd π (homScale π (c 18 6) (lift_17_6_0 π h5)) (homScale π (c 17 6) (lift_17_6_1 π h5))
  | ⟨17,_⟩,⟨7,_⟩ => homScale π (c 18 7) (lift_17_7_0 π h5)
  | ⟨17,_⟩,⟨8,_⟩ => homZero π 17 8
  | ⟨17,_⟩,⟨9,_⟩ => homAdd π (homScale π (c 18 9) (lift_17_9_0 π h5)) (homScale π (c 17 9) (lift_17_9_1 π h5))
  | ⟨17,_⟩,⟨10,_⟩ => homScale π (c 18 10) (lift_17_10_0 π h5)
  | ⟨17,_⟩,⟨11,_⟩ => homScale π (c 18 11) (lift_17_11_0 π h5)
  | ⟨17,_⟩,⟨12,_⟩ => homScale π (c 18 12) (lift_17_12_0 π h5)
  | ⟨17,_⟩,⟨13,_⟩ => homScale π (c 18 13) (lift_17_13_0 π h5)
  | ⟨17,_⟩,⟨14,_⟩ => homScale π (c 18 14) (lift_17_14_0 π h5)
  | ⟨17,_⟩,⟨15,_⟩ => homScale π (c 18 15) (lift_17_15_0 π h5)
  | ⟨17,_⟩,⟨16,_⟩ => homScale π (c 18 16) (lift_17_16_0 π h5)
  | ⟨17,_⟩,⟨17,_⟩ => homAdd π (homScale π (c 18 17) (lift_17_17_0 π h5)) (homScale π (c 17 17) (lift_17_17_1 π h5))
  | ⟨n+18,h⟩,_ => False.elim (by omega)
  | _,⟨n+18,h⟩ => False.elim (by omega)
theorem ell_bounds : ∀ i r, ell i r≤5 := by decide
theorem slot_free : ∀ s, ell (slotVertex s) (part s)=5 := by decide
theorem free_slots : ∀ i r, ell i r=5 ↔ ∃ s : Fin 19, slotVertex s=i ∧ part s=r := by decide
include h5 ann in
lemma residue_ambient (i j : Fin 18) (v : Fin 13 → R) (r c : Fin 3) (hr : ell i r=5) :
    ρ (ambient π i j v r c)=if ell j c=5 then ρ (v ⟨r.val*3+c.val,by omega⟩) else 0 := by
  simp only [ambient,hr,map_mul,map_pow]
  rw [residue_pi π ρ h5 ann]
  by_cases hc : ell j c=5
  · simp [hc]
  · have hn : 5-ell j c≠0 := by have := ell_bounds j c; omega
    simp [hc,zero_pow hn]

def Equivalent (f g : RawMatrix π) : Prop := ∀ i j r c,
  π^(5-ell i r)*π^4*(ambient π i j (f i j).v r c-ambient π i j (g i j).v r c)=0
include h5 ann in
lemma component_exact (i j : Fin 18) (v w : Fin 13 → R) (r c : Fin 3) :
    π^(5-ell i r)*π^4*(ambient π i j v r c-ambient π i j w r c)=0 ↔
    (ell i r=5 → ell j c=5 → ρ (v ⟨r.val*3+c.val,by omega⟩)=ρ (w ⟨r.val*3+c.val,by omega⟩)) := by
  simp only [ambient,← mul_sub,← mul_assoc,← pow_add]
  by_cases hr : ell i r=5
  · by_cases hc : ell j c=5
    · simp [hr,hc,ann,map_sub,sub_eq_zero]
    · have hd : 5≤5-ell i r+4+(ell i r-ell j c) := by have := ell_bounds j c; omega
      rw [high_power π h5 _ hd]
      simp [hc]
  · have hd : 5≤5-ell i r+4+(ell i r-ell j c) := by have := ell_bounds i r; omega
    rw [high_power π h5 _ hd]
    simp [hr]
include h5 ann in
theorem quotient_exact (f g : RawMatrix π) : Equivalent π f g ↔ reduction π ρ f=reduction π ρ g := by
  constructor
  · intro h
    ext r c
    exact (component_exact π ρ h5 ann _ _ _ _ _ _).mp (h _ _ _ _) (slot_free r) (slot_free c)
  · intro h i j r c
    apply (component_exact π ρ h5 ann i j _ _ r c).mpr
    intro hr hc
    obtain ⟨u,rfl,rfl⟩ := (free_slots i r).mp hr
    obtain ⟨v,rfl,rfl⟩ := (free_slots j c).mp hc
    exact congrFun (congrFun h u) v
include h5 ann in
theorem liftValues_spec (M : End k) (v : Mat R) (hv : ∀ i j, ρ (v i j)=M.val i j) :
    reduction π ρ (liftValues π h5 v)=M.val := by
  have hp := residue_pi π ρ h5 ann
  ext r c
  fin_cases r
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_0_0_0,hp,hv]
    · have hz := M.property.1 0 1 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 2 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 6 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 7 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 9 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 10 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 11 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 13 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 14 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 15 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 16 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 17 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 0 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_1_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_1_1_0,hp,hv]
    · have hz := M.property.1 1 2 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 6 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 7 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 9 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 10 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 11 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 13 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 14 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 15 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 16 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 17 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 1 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_2_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_2_1_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_2_2_0,hp,hv]
    · have hz := M.property.1 2 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 2 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 2 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_2_6_0,hp,hv]
    · have hz := M.property.1 2 7 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 2 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_2_9_0,hp,hv]
    · have hz := M.property.1 2 10 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 2 11 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 2 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_2_13_0,hp,hv]
    · have hz := M.property.1 2 14 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 2 15 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 2 16 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_2_17_0,hp,hv]
    · have hz := M.property.1 2 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_2_17_0,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_1_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_2_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_3_0,hp,hv]
    · have hz := M.property.1 3 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 3 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_6_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_7_0,hp,hv]
    · have hz := M.property.1 3 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_9_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_10_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_11_0,hp,hv]
    · have hz := M.property.1 3 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_13_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_14_0,hp,hv]
    · have hz := M.property.1 3 15 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_16_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_17_0,hp,hv]
    · have hz := M.property.1 3 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_3_17_0,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_1_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_2_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_3_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_4_0,hp,hv]
    · have hz := M.property.1 4 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_6_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_7_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_8_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_9_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_10_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_11_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_12_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_13_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_14_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_15_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_16_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_17_0,lift_4_17_1,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_4_17_0,lift_4_17_1,hp,hv]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_1_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_2_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_3_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_4_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_5_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_6_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_7_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_8_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_9_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_10_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_11_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_12_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_13_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_14_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_15_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_16_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_17_0,lift_5_17_1,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_5_17_0,lift_5_17_1,hp,hv]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_6_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_6_1_0,hp,hv]
    · have hz := M.property.1 6 2 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_6_6_0,hp,hv]
    · have hz := M.property.1 6 7 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 9 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 10 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 11 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 13 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 14 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 15 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 16 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 17 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 6 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_7_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_7_1_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_7_2_0,hp,hv]
    · have hz := M.property.1 7 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 7 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 7 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_7_6_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_7_7_0,hp,hv]
    · have hz := M.property.1 7 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_7_9_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_7_10_0,hp,hv]
    · have hz := M.property.1 7 11 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 7 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_7_13_0,hp,hv]
    · have hz := M.property.1 7 14 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 7 15 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_7_16_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_7_17_0,hp,hv]
    · have hz := M.property.1 7 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_7_17_0,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_1_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_2_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_3_0,hp,hv]
    · have hz := M.property.1 8 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 8 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_6_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_7_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_8_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_9_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_10_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_11_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_12_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_13_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_14_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_15_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_16_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_17_0,lift_8_17_1,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_8_17_0,lift_8_17_1,hp,hv]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_9_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_9_1_0,hp,hv]
    · have hz := M.property.1 9 2 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 9 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 9 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 9 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_9_6_0,hp,hv]
    · have hz := M.property.1 9 7 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 9 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_9_9_0,hp,hv]
    · have hz := M.property.1 9 10 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 9 11 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 9 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 9 13 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 9 14 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 9 15 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 9 16 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 9 17 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 9 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_10_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_10_1_0,hp,hv]
    · have hz := M.property.1 10 2 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 10 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 10 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 10 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_10_6_0,hp,hv]
    · have hz := M.property.1 10 7 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 10 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_10_9_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_10_10_0,hp,hv]
    · have hz := M.property.1 10 11 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 10 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 10 13 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 10 14 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 10 15 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 10 16 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_10_17_0,hp,hv]
    · have hz := M.property.1 10 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_10_17_0,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_11_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_11_1_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_11_2_0,hp,hv]
    · have hz := M.property.1 11 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 11 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 11 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_11_6_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_11_7_0,hp,hv]
    · have hz := M.property.1 11 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_11_9_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_11_10_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_11_11_0,hp,hv]
    · have hz := M.property.1 11 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_11_13_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_11_14_0,hp,hv]
    · have hz := M.property.1 11 15 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_11_16_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_11_17_0,hp,hv]
    · have hz := M.property.1 11 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_11_17_0,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_1_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_2_0,hp,hv]
    · have hz := M.property.1 12 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 12 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 12 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_6_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_7_0,hp,hv]
    · have hz := M.property.1 12 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_9_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_10_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_11_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_12_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_13_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_14_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_15_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_16_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_17_0,hp,hv]
    · have hz := M.property.1 12 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_12_17_0,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_13_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_13_1_0,hp,hv]
    · have hz := M.property.1 13 2 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 13 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 13 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 13 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_13_6_0,hp,hv]
    · have hz := M.property.1 13 7 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 13 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_13_9_0,hp,hv]
    · have hz := M.property.1 13 10 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 13 11 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 13 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_13_13_0,hp,hv]
    · have hz := M.property.1 13 14 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 13 15 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 13 16 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_13_17_0,hp,hv]
    · have hz := M.property.1 13 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_13_17_0,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_14_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_14_1_0,hp,hv]
    · have hz := M.property.1 14 2 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 14 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 14 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 14 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_14_6_0,hp,hv]
    · have hz := M.property.1 14 7 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 14 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_14_9_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_14_10_0,hp,hv]
    · have hz := M.property.1 14 11 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 14 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_14_13_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_14_14_0,hp,hv]
    · have hz := M.property.1 14 15 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_14_16_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_14_17_0,hp,hv]
    · have hz := M.property.1 14 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_14_17_0,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_15_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_15_1_0,hp,hv]
    · have hz := M.property.1 15 2 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 15 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 15 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 15 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_15_6_0,hp,hv]
    · have hz := M.property.1 15 7 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 15 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_15_9_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_15_10_0,hp,hv]
    · have hz := M.property.1 15 11 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 15 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_15_13_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_15_14_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_15_15_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_15_16_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_15_17_0,hp,hv]
    · have hz := M.property.1 15 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_15_17_0,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_16_0_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_16_1_0,hp,hv]
    · have hz := M.property.1 16 2 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 16 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 16 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 16 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_16_6_0,hp,hv]
    · have hz := M.property.1 16 7 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 16 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_16_9_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_16_10_0,hp,hv]
    · have hz := M.property.1 16 11 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 16 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_16_13_0,hp,hv]
    · have hz := M.property.1 16 14 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 16 15 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_16_16_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_16_17_0,hp,hv]
    · have hz := M.property.1 16 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_16_17_0,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_0_0,lift_17_0_1,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_1_0,lift_17_1_1,hp,hv]
    · have hz := M.property.1 17 2 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_2_0,hp,hv,hz]
    · have hz := M.property.1 17 3 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_3_0,hp,hv,hz]
    · have hz := M.property.1 17 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 17 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_6_0,lift_17_6_1,hp,hv]
    · have hz := M.property.1 17 7 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_7_0,hp,hv,hz]
    · have hz := M.property.1 17 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_9_0,lift_17_9_1,hp,hv]
    · have hz := M.property.1 17 10 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_10_0,hp,hv,hz]
    · have hz := M.property.1 17 11 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_11_0,hp,hv,hz]
    · have hz := M.property.1 17 12 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_12_0,hp,hv,hz]
    · have hz := M.property.1 17 13 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_13_0,hp,hv,hz]
    · have hz := M.property.1 17 14 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_14_0,hp,hv,hz]
    · have hz := M.property.1 17 15 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_15_0,hp,hv,hz]
    · have hz := M.property.1 17 16 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_16_0,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_17_0,lift_17_17_1,hp,hv]
    · have hz := M.property.1 17 18 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_17_0,lift_17_17_1,hp,hv,hz]
  · fin_cases c
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_0_0,lift_17_0_1,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_1_0,lift_17_1_1,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_2_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_3_0,hp,hv]
    · have hz := M.property.1 18 4 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · have hz := M.property.1 18 5 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_6_0,lift_17_6_1,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_7_0,hp,hv]
    · have hz := M.property.1 18 8 (by decide)
      simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,hp,hv,hz]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_9_0,lift_17_9_1,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_10_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_11_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_12_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_13_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_14_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_15_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_16_0,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_17_0,lift_17_17_1,hp,hv]
    · simp [reduction,liftValues,part,slotVertex,homZero,homAdd,homScale,lift_17_17_0,lift_17_17_1,hp,hv]
      exact M.property.2
include h5 ann in
theorem reduce_surjective (surj : Function.Surjective ρ) : Function.Surjective (reduce π ρ h5 ann) := by
  intro M
  choose v hv using (fun i j => surj (M.val i j))
  refine ⟨liftValues π h5 v,?_⟩
  apply Subtype.ext
  exact liftValues_spec π ρ h5 ann M v hv
lemma sum_free_slots (F : Fin 18 → Fin 3 → k) :
    (∑ i, ∑ r, if ell i r=5 then F i r else 0) = ∑ s : Fin 19, F (slotVertex s) (part s) := by
  simp [Fin.sum_univ_succ,ell,slotVertex,part]
  <;> ring
include h5 ann in
/-- Ambient block composition reduces to multiplication of the surviving free blocks. -/
theorem reduce_composition (f g : RawMatrix π) (r c : Fin 19) :
    ρ (∑ i : Fin 18,
      (ambient π (slotVertex r) i (f (slotVertex r) i).v *
       ambient π i (slotVertex c) (g i (slotVertex c)).v) (part r) (part c)) =
    (reduction π ρ f*reduction π ρ g) r c := by
  simp only [Matrix.mul_apply,map_sum,map_mul]
  have he : (∑ i : Fin 18, ∑ l : Fin 3,
      ρ (ambient π (slotVertex r) i (f (slotVertex r) i).v (part r) l)*
      ρ (ambient π i (slotVertex c) (g i (slotVertex c)).v l (part c))) =
      ∑ i : Fin 18, ∑ l : Fin 3, if ell i l=5 then
        ρ ((f (slotVertex r) i).v ⟨(part r).val*3+l.val,by omega⟩)*
        ρ ((g i (slotVertex c)).v ⟨l.val*3+(part c).val,by omega⟩) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    rw [residue_ambient π ρ h5 ann _ _ _ _ _ (slot_free r)]
    by_cases hl : ell i l=5
    · rw [if_pos hl,residue_ambient π ρ h5 ann _ _ _ _ _ hl,if_pos (slot_free c),if_pos hl]
    · rw [if_neg hl,if_neg hl,zero_mul]
  rw [he,sum_free_slots]
  rfl

end UniserialComputations.N5.Raw
