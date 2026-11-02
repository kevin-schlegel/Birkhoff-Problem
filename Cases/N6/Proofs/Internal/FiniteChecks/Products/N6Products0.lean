import N6CompositionData
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
theorem compatible_0_0_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 0 p*basisInt 0 q) := by decide
theorem compatible_0_0_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 0 p*basisInt 0 q) := by decide
theorem compatible_0_0_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 0 p*basisInt 0 q) := by decide
theorem compatible_0_1_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 0 p*basisInt 1 q) := by decide
theorem compatible_0_1_1 : ∀ p q : Fin 3, Normal ℤ 1 (basisInt 0 p*basisInt 1 q) := by decide
theorem compatible_0_1_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 0 p*basisInt 1 q) := by decide
theorem compatible_0_1_4 : ∀ p q : Fin 3, Normal ℤ 4 (basisInt 0 p*basisInt 1 q) := by decide
theorem compatible_0_1_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 0 p*basisInt 1 q) := by decide
theorem compatible_0_1_10 : ∀ p q : Fin 3, Normal ℤ 10 (basisInt 0 p*basisInt 1 q) := by decide
theorem compatible_0_1_11 : ∀ p q : Fin 3, Normal ℤ 11 (basisInt 0 p*basisInt 1 q) := by decide
theorem compatible_0_1_12 : ∀ p q : Fin 3, Normal ℤ 12 (basisInt 0 p*basisInt 1 q) := by decide
theorem compatible_0_2_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 0 p*basisInt 2 q) := by decide
theorem compatible_0_2_1 : ∀ p q : Fin 3, Normal ℤ 1 (basisInt 0 p*basisInt 2 q) := by decide
theorem compatible_0_2_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 0 p*basisInt 2 q) := by decide
theorem compatible_0_3_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 0 p*basisInt 3 q) := by decide
theorem compatible_0_4_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 0 p*basisInt 4 q) := by decide
theorem compatible_0_5_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 0 p*basisInt 5 q) := by decide
theorem compatible_0_6_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 0 p*basisInt 6 q) := by decide
theorem compatible_0_6_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 0 p*basisInt 6 q) := by decide
theorem compatible_0_7_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 0 p*basisInt 7 q) := by decide
theorem compatible_0_7_1 : ∀ p q : Fin 3, Normal ℤ 1 (basisInt 0 p*basisInt 7 q) := by decide
theorem compatible_0_7_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 0 p*basisInt 7 q) := by decide
theorem compatible_0_7_10 : ∀ p q : Fin 3, Normal ℤ 10 (basisInt 0 p*basisInt 7 q) := by decide
theorem compatible_0_7_11 : ∀ p q : Fin 3, Normal ℤ 11 (basisInt 0 p*basisInt 7 q) := by decide
theorem compatible_0_8_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 0 p*basisInt 8 q) := by decide
theorem compatible_0_8_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 0 p*basisInt 8 q) := by decide
theorem compatible_0_9_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 0 p*basisInt 9 q) := by decide
theorem compatible_0_9_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 0 p*basisInt 9 q) := by decide
theorem compatible_0_10_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 0 p*basisInt 10 q) := by decide
theorem compatible_0_10_10 : ∀ p q : Fin 3, Normal ℤ 10 (basisInt 0 p*basisInt 10 q) := by decide
theorem compatible_0_11_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 0 p*basisInt 11 q) := by decide
theorem compatible_0_11_11 : ∀ p q : Fin 3, Normal ℤ 11 (basisInt 0 p*basisInt 11 q) := by decide
theorem compatible_0_12_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 0 p*basisInt 12 q) := by decide
theorem compatible_0_13_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 0 p*basisInt 13 q) := by decide
theorem compatible_0_13_1 : ∀ p q : Fin 3, Normal ℤ 1 (basisInt 0 p*basisInt 13 q) := by decide
theorem compatible_0_13_10 : ∀ p q : Fin 3, Normal ℤ 10 (basisInt 0 p*basisInt 13 q) := by decide
theorem products_row0 (b c : Fin 14) (h : Allowed 0 b c) (p q : Fin 3) : Normal ℤ c (basisInt 0 p*basisInt b q) := by
  fin_cases b <;> fin_cases c
  · exact compatible_0_0_0 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_0_3 p q
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_0_5 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_1_0 p q
  · exact compatible_0_1_1 p q
  · exact compatible_0_1_2 p q
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_1_4 p q
  · exact compatible_0_1_5 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_1_10 p q
  · exact compatible_0_1_11 p q
  · exact compatible_0_1_12 p q
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_2_0 p q
  · exact compatible_0_2_1 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_2_5 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_3_0 p q
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
  · exact compatible_0_4_0 p q
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
  · exact compatible_0_5_5 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_6_0 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_6_5 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_7_0 p q
  · exact compatible_0_7_1 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_7_5 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_7_10 p q
  · exact compatible_0_7_11 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_8_0 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_8_5 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_9_0 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_9_5 p q
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
  · exact compatible_0_10_5 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_10_10 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_11_5 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_11_11 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_12_0 p q
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
  · exact compatible_0_13_0 p q
  · exact compatible_0_13_1 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_0_13_10 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
end UniserialComputations.N6
