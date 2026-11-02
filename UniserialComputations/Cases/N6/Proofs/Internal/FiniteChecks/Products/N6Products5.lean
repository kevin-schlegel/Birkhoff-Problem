import N6CompositionData
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
theorem compatible_5_0_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 5 p*basisInt 0 q) := by decide
theorem compatible_5_1_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 5 p*basisInt 1 q) := by decide
theorem compatible_5_1_1 : ∀ p q : Fin 3, Normal ℤ 1 (basisInt 5 p*basisInt 1 q) := by decide
theorem compatible_5_1_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 5 p*basisInt 1 q) := by decide
theorem compatible_5_2_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 5 p*basisInt 2 q) := by decide
theorem compatible_5_2_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 5 p*basisInt 2 q) := by decide
theorem compatible_5_3_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 5 p*basisInt 3 q) := by decide
theorem compatible_5_3_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 5 p*basisInt 3 q) := by decide
theorem compatible_5_4_0 : ∀ p q : Fin 3, Normal ℤ 0 (basisInt 5 p*basisInt 4 q) := by decide
theorem compatible_5_4_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 5 p*basisInt 4 q) := by decide
theorem compatible_5_6_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 5 p*basisInt 6 q) := by decide
theorem compatible_5_7_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 5 p*basisInt 7 q) := by decide
theorem compatible_5_8_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 5 p*basisInt 8 q) := by decide
theorem compatible_5_9_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 5 p*basisInt 9 q) := by decide
theorem compatible_5_12_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 5 p*basisInt 12 q) := by decide
theorem compatible_5_13_5 : ∀ p q : Fin 3, Normal ℤ 5 (basisInt 5 p*basisInt 13 q) := by decide
theorem compatible_5_13_11 : ∀ p q : Fin 3, Normal ℤ 11 (basisInt 5 p*basisInt 13 q) := by decide
theorem products_row5 (b c : Fin 14) (h : Allowed 5 b c) (p q : Fin 3) : Normal ℤ c (basisInt 5 p*basisInt b q) := by
  fin_cases b <;> fin_cases c
  · exact compatible_5_0_0 p q
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
  · exact compatible_5_1_0 p q
  · exact compatible_5_1_1 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_5_1_5 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_5_2_0 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_5_2_5 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_5_3_0 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_5_3_5 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_5_4_0 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_5_4_5 p q
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
  · exact compatible_5_6_5 p q
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
  · exact compatible_5_7_5 p q
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
  · exact compatible_5_8_5 p q
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
  · exact compatible_5_9_5 p q
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
  · exact compatible_5_12_5 p q
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
  · exact compatible_5_13_5 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_5_13_11 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
end UniserialComputations.N6
