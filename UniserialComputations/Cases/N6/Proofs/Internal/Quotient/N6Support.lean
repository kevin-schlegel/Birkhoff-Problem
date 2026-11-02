import N6Total
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
def GoodEntry (i j : Fin 47) (b : Fin 3) (r c : Fin 2) : Prop :=
  ¬(r.val<freeRank i ∧ c.val<freeRank j) → basisInt (homKind i j) b r c=0
instance (i j : Fin 47) (b : Fin 3) (r c : Fin 2) : Decidable (GoodEntry i j b r c) := by
  unfold GoodEntry
  infer_instance
theorem basis_padding_0 : ∀ j b r c, GoodEntry 0 j b r c := by decide
theorem basis_padding_1 : ∀ j b r c, GoodEntry 1 j b r c := by decide
theorem basis_padding_2 : ∀ j b r c, GoodEntry 2 j b r c := by decide
theorem basis_padding_3 : ∀ j b r c, GoodEntry 3 j b r c := by decide
theorem basis_padding_4 : ∀ j b r c, GoodEntry 4 j b r c := by decide
theorem basis_padding_5 : ∀ j b r c, GoodEntry 5 j b r c := by decide
theorem basis_padding_6 : ∀ j b r c, GoodEntry 6 j b r c := by decide
theorem basis_padding_7 : ∀ j b r c, GoodEntry 7 j b r c := by decide
theorem basis_padding_8 : ∀ j b r c, GoodEntry 8 j b r c := by decide
theorem basis_padding_9 : ∀ j b r c, GoodEntry 9 j b r c := by decide
theorem basis_padding_10 : ∀ j b r c, GoodEntry 10 j b r c := by decide
theorem basis_padding_11 : ∀ j b r c, GoodEntry 11 j b r c := by decide
theorem basis_padding_12 : ∀ j b r c, GoodEntry 12 j b r c := by decide
theorem basis_padding_13 : ∀ j b r c, GoodEntry 13 j b r c := by decide
theorem basis_padding_14 : ∀ j b r c, GoodEntry 14 j b r c := by decide
theorem basis_padding_15 : ∀ j b r c, GoodEntry 15 j b r c := by decide
theorem basis_padding_16 : ∀ j b r c, GoodEntry 16 j b r c := by decide
theorem basis_padding_17 : ∀ j b r c, GoodEntry 17 j b r c := by decide
theorem basis_padding_18 : ∀ j b r c, GoodEntry 18 j b r c := by decide
theorem basis_padding_19 : ∀ j b r c, GoodEntry 19 j b r c := by decide
theorem basis_padding_20 : ∀ j b r c, GoodEntry 20 j b r c := by decide
theorem basis_padding_21 : ∀ j b r c, GoodEntry 21 j b r c := by decide
theorem basis_padding_22 : ∀ j b r c, GoodEntry 22 j b r c := by decide
theorem basis_padding_23 : ∀ j b r c, GoodEntry 23 j b r c := by decide
theorem basis_padding_24 : ∀ j b r c, GoodEntry 24 j b r c := by decide
theorem basis_padding_25 : ∀ j b r c, GoodEntry 25 j b r c := by decide
theorem basis_padding_26 : ∀ j b r c, GoodEntry 26 j b r c := by decide
theorem basis_padding_27 : ∀ j b r c, GoodEntry 27 j b r c := by decide
theorem basis_padding_28 : ∀ j b r c, GoodEntry 28 j b r c := by decide
theorem basis_padding_29 : ∀ j b r c, GoodEntry 29 j b r c := by decide
theorem basis_padding_30 : ∀ j b r c, GoodEntry 30 j b r c := by decide
theorem basis_padding_31 : ∀ j b r c, GoodEntry 31 j b r c := by decide
theorem basis_padding_32 : ∀ j b r c, GoodEntry 32 j b r c := by decide
theorem basis_padding_33 : ∀ j b r c, GoodEntry 33 j b r c := by decide
theorem basis_padding_34 : ∀ j b r c, GoodEntry 34 j b r c := by decide
theorem basis_padding_35 : ∀ j b r c, GoodEntry 35 j b r c := by decide
theorem basis_padding_36 : ∀ j b r c, GoodEntry 36 j b r c := by decide
theorem basis_padding_37 : ∀ j b r c, GoodEntry 37 j b r c := by decide
theorem basis_padding_38 : ∀ j b r c, GoodEntry 38 j b r c := by decide
theorem basis_padding_39 : ∀ j b r c, GoodEntry 39 j b r c := by decide
theorem basis_padding_40 : ∀ j b r c, GoodEntry 40 j b r c := by decide
theorem basis_padding_41 : ∀ j b r c, GoodEntry 41 j b r c := by decide
theorem basis_padding_42 : ∀ j b r c, GoodEntry 42 j b r c := by decide
theorem basis_padding_43 : ∀ j b r c, GoodEntry 43 j b r c := by decide
theorem basis_padding_44 : ∀ j b r c, GoodEntry 44 j b r c := by decide
theorem basis_padding_45 : ∀ j b r c, GoodEntry 45 j b r c := by decide
theorem basis_padding_46 : ∀ j b r c, GoodEntry 46 j b r c := by decide
theorem basis_padding (i j : Fin 47) (b : Fin 3) (r c : Fin 2) (h : ¬(r.val<freeRank i ∧ c.val<freeRank j)) : basisInt (homKind i j) b r c=0 := by
  fin_cases i
  · exact basis_padding_0 j b r c h
  · exact basis_padding_1 j b r c h
  · exact basis_padding_2 j b r c h
  · exact basis_padding_3 j b r c h
  · exact basis_padding_4 j b r c h
  · exact basis_padding_5 j b r c h
  · exact basis_padding_6 j b r c h
  · exact basis_padding_7 j b r c h
  · exact basis_padding_8 j b r c h
  · exact basis_padding_9 j b r c h
  · exact basis_padding_10 j b r c h
  · exact basis_padding_11 j b r c h
  · exact basis_padding_12 j b r c h
  · exact basis_padding_13 j b r c h
  · exact basis_padding_14 j b r c h
  · exact basis_padding_15 j b r c h
  · exact basis_padding_16 j b r c h
  · exact basis_padding_17 j b r c h
  · exact basis_padding_18 j b r c h
  · exact basis_padding_19 j b r c h
  · exact basis_padding_20 j b r c h
  · exact basis_padding_21 j b r c h
  · exact basis_padding_22 j b r c h
  · exact basis_padding_23 j b r c h
  · exact basis_padding_24 j b r c h
  · exact basis_padding_25 j b r c h
  · exact basis_padding_26 j b r c h
  · exact basis_padding_27 j b r c h
  · exact basis_padding_28 j b r c h
  · exact basis_padding_29 j b r c h
  · exact basis_padding_30 j b r c h
  · exact basis_padding_31 j b r c h
  · exact basis_padding_32 j b r c h
  · exact basis_padding_33 j b r c h
  · exact basis_padding_34 j b r c h
  · exact basis_padding_35 j b r c h
  · exact basis_padding_36 j b r c h
  · exact basis_padding_37 j b r c h
  · exact basis_padding_38 j b r c h
  · exact basis_padding_39 j b r c h
  · exact basis_padding_40 j b r c h
  · exact basis_padding_41 j b r c h
  · exact basis_padding_42 j b r c h
  · exact basis_padding_43 j b r c h
  · exact basis_padding_44 j b r c h
  · exact basis_padding_45 j b r c h
  · exact basis_padding_46 j b r c h
variable (k : Type*) [CommRing k]
theorem normal_padded (i j : Fin 47) {A : Block k} (h : Normal k (homKind i j) A) : Padded k i j A := by
  intro r c hc
  have hh := congrFun (congrFun h r) c
  change (∑ b : Fin 3,coords k (homKind i j) A b • basisBlock k (homKind i j) b) r c=A r c at hh
  simpa only [Matrix.sum_apply,Matrix.smul_apply,basisBlock,basis_padding i j _ r c hc,Int.cast_zero,smul_zero,Finset.sum_const_zero] using hh.symm
end UniserialComputations.N6
