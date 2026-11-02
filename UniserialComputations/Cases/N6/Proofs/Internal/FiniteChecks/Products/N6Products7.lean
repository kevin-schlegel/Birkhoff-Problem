import N6CompositionData
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
theorem compatible_7_0_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 7 p*basisInt 0 q) := by decide
theorem compatible_7_1_1 : ∀ p q : Fin 3, Normal ℤ 1 (basisInt 7 p*basisInt 1 q) := by decide
theorem compatible_7_1_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 7 p*basisInt 1 q) := by decide
theorem compatible_7_1_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 7 p*basisInt 1 q) := by decide
theorem compatible_7_2_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 7 p*basisInt 2 q) := by decide
theorem compatible_7_2_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 7 p*basisInt 2 q) := by decide
theorem compatible_7_3_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 7 p*basisInt 3 q) := by decide
theorem compatible_7_3_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 7 p*basisInt 3 q) := by decide
theorem compatible_7_3_6 : ∀ p q : Fin 3, Normal ℤ 6 (basisInt 7 p*basisInt 3 q) := by decide
theorem compatible_7_3_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 7 p*basisInt 3 q) := by decide
theorem compatible_7_3_8 : ∀ p q : Fin 3, Normal ℤ 8 (basisInt 7 p*basisInt 3 q) := by decide
theorem compatible_7_3_9 : ∀ p q : Fin 3, Normal ℤ 9 (basisInt 7 p*basisInt 3 q) := by decide
theorem compatible_7_4_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 7 p*basisInt 4 q) := by decide
theorem compatible_7_4_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 7 p*basisInt 4 q) := by decide
theorem compatible_7_4_6 : ∀ p q : Fin 3, Normal ℤ 6 (basisInt 7 p*basisInt 4 q) := by decide
theorem compatible_7_4_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 7 p*basisInt 4 q) := by decide
theorem compatible_7_6_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 7 p*basisInt 6 q) := by decide
theorem compatible_7_7_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 7 p*basisInt 7 q) := by decide
theorem compatible_7_8_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 7 p*basisInt 8 q) := by decide
theorem compatible_7_9_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 7 p*basisInt 9 q) := by decide
theorem compatible_7_12_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 7 p*basisInt 12 q) := by decide
theorem compatible_7_13_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 7 p*basisInt 13 q) := by decide
theorem products_row7 (b c : Fin 14) (h : Allowed 7 b c) (p q : Fin 3) : Normal ℤ c (basisInt 7 p*basisInt b q) := by
  fin_cases b <;> fin_cases c
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_7_0_2 p q
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
  · exact compatible_7_1_1 p q
  · exact compatible_7_1_2 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_7_1_7 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_7_2_2 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_7_2_7 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_7_3_2 p q
  · exact compatible_7_3_3 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_7_3_6 p q
  · exact compatible_7_3_7 p q
  · exact compatible_7_3_8 p q
  · exact compatible_7_3_9 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_7_4_2 p q
  · exact compatible_7_4_3 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_7_4_6 p q
  · exact compatible_7_4_7 p q
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
  · exact compatible_7_6_7 p q
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
  · exact compatible_7_7_7 p q
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
  · exact compatible_7_8_7 p q
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
  · exact compatible_7_9_7 p q
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
  · exact compatible_7_12_7 p q
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
  · exact compatible_7_13_7 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
end UniserialComputations.N6
