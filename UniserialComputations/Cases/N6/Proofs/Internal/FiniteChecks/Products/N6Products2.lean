import N6CompositionData
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
theorem compatible_2_0_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 2 p*basisInt 0 q) := by decide
theorem compatible_2_0_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 2 p*basisInt 0 q) := by decide
theorem compatible_2_0_6 : ∀ p q : Fin 3, Normal ℤ 6 (basisInt 2 p*basisInt 0 q) := by decide
theorem compatible_2_0_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 2 p*basisInt 0 q) := by decide
theorem compatible_2_0_8 : ∀ p q : Fin 3, Normal ℤ 8 (basisInt 2 p*basisInt 0 q) := by decide
theorem compatible_2_0_9 : ∀ p q : Fin 3, Normal ℤ 9 (basisInt 2 p*basisInt 0 q) := by decide
theorem compatible_2_1_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 2 p*basisInt 1 q) := by decide
theorem compatible_2_1_1 : ∀ p q : Fin 3, Normal ℤ 1 (basisInt 2 p*basisInt 1 q) := by decide
theorem compatible_2_1_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 2 p*basisInt 1 q) := by decide
theorem compatible_2_1_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 2 p*basisInt 1 q) := by decide
theorem compatible_2_1_4 : ∀ p q : Fin 3, Normal ℤ 4 (basisInt 2 p*basisInt 1 q) := by decide
theorem compatible_2_1_6 : ∀ p q : Fin 3, Normal ℤ 6 (basisInt 2 p*basisInt 1 q) := by decide
theorem compatible_2_1_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 2 p*basisInt 1 q) := by decide
theorem compatible_2_1_8 : ∀ p q : Fin 3, Normal ℤ 8 (basisInt 2 p*basisInt 1 q) := by decide
theorem compatible_2_1_12 : ∀ p q : Fin 3, Normal ℤ 12 (basisInt 2 p*basisInt 1 q) := by decide
theorem compatible_2_1_13 : ∀ p q : Fin 3, Normal ℤ 13 (basisInt 2 p*basisInt 1 q) := by decide
theorem compatible_2_2_1 : ∀ p q : Fin 3, Normal ℤ 1 (basisInt 2 p*basisInt 2 q) := by decide
theorem compatible_2_2_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 2 p*basisInt 2 q) := by decide
theorem compatible_2_2_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 2 p*basisInt 2 q) := by decide
theorem compatible_2_2_6 : ∀ p q : Fin 3, Normal ℤ 6 (basisInt 2 p*basisInt 2 q) := by decide
theorem compatible_2_3_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 2 p*basisInt 3 q) := by decide
theorem compatible_2_3_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 2 p*basisInt 3 q) := by decide
theorem compatible_2_5_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 2 p*basisInt 5 q) := by decide
theorem compatible_2_5_8 : ∀ p q : Fin 3, Normal ℤ 8 (basisInt 2 p*basisInt 5 q) := by decide
theorem compatible_2_6_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 2 p*basisInt 6 q) := by decide
theorem compatible_2_6_6 : ∀ p q : Fin 3, Normal ℤ 6 (basisInt 2 p*basisInt 6 q) := by decide
theorem compatible_2_6_8 : ∀ p q : Fin 3, Normal ℤ 8 (basisInt 2 p*basisInt 6 q) := by decide
theorem compatible_2_7_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 2 p*basisInt 7 q) := by decide
theorem compatible_2_7_13 : ∀ p q : Fin 3, Normal ℤ 13 (basisInt 2 p*basisInt 7 q) := by decide
theorem compatible_2_8_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 2 p*basisInt 8 q) := by decide
theorem compatible_2_8_6 : ∀ p q : Fin 3, Normal ℤ 6 (basisInt 2 p*basisInt 8 q) := by decide
theorem compatible_2_8_8 : ∀ p q : Fin 3, Normal ℤ 8 (basisInt 2 p*basisInt 8 q) := by decide
theorem compatible_2_8_9 : ∀ p q : Fin 3, Normal ℤ 9 (basisInt 2 p*basisInt 8 q) := by decide
theorem compatible_2_9_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 2 p*basisInt 9 q) := by decide
theorem compatible_2_9_6 : ∀ p q : Fin 3, Normal ℤ 6 (basisInt 2 p*basisInt 9 q) := by decide
theorem compatible_2_10_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 2 p*basisInt 10 q) := by decide
theorem compatible_2_11_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 2 p*basisInt 11 q) := by decide
theorem products_row2 (b c : Fin 14) (h : Allowed 2 b c) (p q : Fin 3) : Normal ℤ c (basisInt 2 p*basisInt b q) := by
  fin_cases b <;> fin_cases c
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_0_2 p q
  · exact compatible_2_0_3 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_0_6 p q
  · exact compatible_2_0_7 p q
  · exact compatible_2_0_8 p q
  · exact compatible_2_0_9 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_1_0 p q
  · exact compatible_2_1_1 p q
  · exact compatible_2_1_2 p q
  · exact compatible_2_1_3 p q
  · exact compatible_2_1_4 p q
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_1_6 p q
  · exact compatible_2_1_7 p q
  · exact compatible_2_1_8 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_1_12 p q
  · exact compatible_2_1_13 p q
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_2_1 p q
  · exact compatible_2_2_2 p q
  · exact compatible_2_2_3 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_2_6 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_3_2 p q
  · exact compatible_2_3_3 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_5_7 p q
  · exact compatible_2_5_8 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_6_2 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_6_6 p q
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_6_8 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_7_7 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_7_13 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_8_2 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_8_6 p q
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_8_8 p q
  · exact compatible_2_8_9 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_9_2 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_9_6 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_10_7 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_2_11_7 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
end UniserialComputations.N6
