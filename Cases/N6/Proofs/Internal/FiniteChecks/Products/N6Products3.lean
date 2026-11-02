import N6CompositionData
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
theorem compatible_3_0_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 3 p*basisInt 0 q) := by decide
theorem compatible_3_0_8 : ∀ p q : Fin 3, Normal ℤ 8 (basisInt 3 p*basisInt 0 q) := by decide
theorem compatible_3_1_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 3 p*basisInt 1 q) := by decide
theorem compatible_3_1_1 : ∀ p q : Fin 3, Normal ℤ 1 (basisInt 3 p*basisInt 1 q) := by decide
theorem compatible_3_1_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 3 p*basisInt 1 q) := by decide
theorem compatible_3_1_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 3 p*basisInt 1 q) := by decide
theorem compatible_3_1_4 : ∀ p q : Fin 3, Normal ℤ 4 (basisInt 3 p*basisInt 1 q) := by decide
theorem compatible_3_1_6 : ∀ p q : Fin 3, Normal ℤ 6 (basisInt 3 p*basisInt 1 q) := by decide
theorem compatible_3_1_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 3 p*basisInt 1 q) := by decide
theorem compatible_3_1_8 : ∀ p q : Fin 3, Normal ℤ 8 (basisInt 3 p*basisInt 1 q) := by decide
theorem compatible_3_1_9 : ∀ p q : Fin 3, Normal ℤ 9 (basisInt 3 p*basisInt 1 q) := by decide
theorem compatible_3_1_12 : ∀ p q : Fin 3, Normal ℤ 12 (basisInt 3 p*basisInt 1 q) := by decide
theorem compatible_3_1_13 : ∀ p q : Fin 3, Normal ℤ 13 (basisInt 3 p*basisInt 1 q) := by decide
theorem compatible_3_2_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 3 p*basisInt 2 q) := by decide
theorem compatible_3_2_1 : ∀ p q : Fin 3, Normal ℤ 1 (basisInt 3 p*basisInt 2 q) := by decide
theorem compatible_3_2_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 3 p*basisInt 2 q) := by decide
theorem compatible_3_2_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 3 p*basisInt 2 q) := by decide
theorem compatible_3_2_4 : ∀ p q : Fin 3, Normal ℤ 4 (basisInt 3 p*basisInt 2 q) := by decide
theorem compatible_3_3_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 3 p*basisInt 3 q) := by decide
theorem compatible_3_6_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 3 p*basisInt 6 q) := by decide
theorem compatible_3_7_1 : ∀ p q : Fin 3, Normal ℤ 1 (basisInt 3 p*basisInt 7 q) := by decide
theorem compatible_3_7_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 3 p*basisInt 7 q) := by decide
theorem compatible_3_7_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 3 p*basisInt 7 q) := by decide
theorem compatible_3_7_4 : ∀ p q : Fin 3, Normal ℤ 4 (basisInt 3 p*basisInt 7 q) := by decide
theorem compatible_3_7_6 : ∀ p q : Fin 3, Normal ℤ 6 (basisInt 3 p*basisInt 7 q) := by decide
theorem compatible_3_7_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 3 p*basisInt 7 q) := by decide
theorem compatible_3_7_8 : ∀ p q : Fin 3, Normal ℤ 8 (basisInt 3 p*basisInt 7 q) := by decide
theorem compatible_3_7_9 : ∀ p q : Fin 3, Normal ℤ 9 (basisInt 3 p*basisInt 7 q) := by decide
theorem compatible_3_7_12 : ∀ p q : Fin 3, Normal ℤ 12 (basisInt 3 p*basisInt 7 q) := by decide
theorem compatible_3_7_13 : ∀ p q : Fin 3, Normal ℤ 13 (basisInt 3 p*basisInt 7 q) := by decide
theorem compatible_3_8_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 3 p*basisInt 8 q) := by decide
theorem compatible_3_9_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 3 p*basisInt 9 q) := by decide
theorem compatible_3_13_12 : ∀ p q : Fin 3, Normal ℤ 12 (basisInt 3 p*basisInt 13 q) := by decide
theorem products_row3 (b c : Fin 14) (h : Allowed 3 b c) (p q : Fin 3) : Normal ℤ c (basisInt 3 p*basisInt b q) := by
  fin_cases b <;> fin_cases c
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_3_0_3 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_3_0_8 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_3_1_0 p q
  · exact compatible_3_1_1 p q
  · exact compatible_3_1_2 p q
  · exact compatible_3_1_3 p q
  · exact compatible_3_1_4 p q
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_3_1_6 p q
  · exact compatible_3_1_7 p q
  · exact compatible_3_1_8 p q
  · exact compatible_3_1_9 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_3_1_12 p q
  · exact compatible_3_1_13 p q
  · exact compatible_3_2_0 p q
  · exact compatible_3_2_1 p q
  · exact compatible_3_2_2 p q
  · exact compatible_3_2_3 p q
  · exact compatible_3_2_4 p q
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
  · exact compatible_3_3_3 p q
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
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_3_6_3 p q
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
  · exact compatible_3_7_1 p q
  · exact compatible_3_7_2 p q
  · exact compatible_3_7_3 p q
  · exact compatible_3_7_4 p q
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_3_7_6 p q
  · exact compatible_3_7_7 p q
  · exact compatible_3_7_8 p q
  · exact compatible_3_7_9 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_3_7_12 p q
  · exact compatible_3_7_13 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_3_8_3 p q
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
  · exact compatible_3_9_3 p q
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
  · exact compatible_3_13_12 p q
  · norm_num [Allowed,allowedTargets] at h
end UniserialComputations.N6
