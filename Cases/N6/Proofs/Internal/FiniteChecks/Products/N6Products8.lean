import N6CompositionData
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
theorem compatible_8_1_1 : ∀ p q : Fin 3, Normal ℤ 1 (basisInt 8 p*basisInt 1 q) := by decide
theorem compatible_8_1_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 8 p*basisInt 1 q) := by decide
theorem compatible_8_1_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 8 p*basisInt 1 q) := by decide
theorem compatible_8_1_6 : ∀ p q : Fin 3, Normal ℤ 6 (basisInt 8 p*basisInt 1 q) := by decide
theorem compatible_8_2_2 : ∀ p q : Fin 3, Normal ℤ 2 (basisInt 8 p*basisInt 2 q) := by decide
theorem compatible_8_2_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 8 p*basisInt 2 q) := by decide
theorem compatible_8_2_6 : ∀ p q : Fin 3, Normal ℤ 6 (basisInt 8 p*basisInt 2 q) := by decide
theorem compatible_8_2_8 : ∀ p q : Fin 3, Normal ℤ 8 (basisInt 8 p*basisInt 2 q) := by decide
theorem compatible_8_3_3 : ∀ p q : Fin 3, Normal ℤ 3 (basisInt 8 p*basisInt 3 q) := by decide
theorem compatible_8_6_8 : ∀ p q : Fin 3, Normal ℤ 8 (basisInt 8 p*basisInt 6 q) := by decide
theorem compatible_8_7_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 8 p*basisInt 7 q) := by decide
theorem compatible_8_8_8 : ∀ p q : Fin 3, Normal ℤ 8 (basisInt 8 p*basisInt 8 q) := by decide
theorem compatible_8_9_8 : ∀ p q : Fin 3, Normal ℤ 8 (basisInt 8 p*basisInt 9 q) := by decide
theorem compatible_8_13_7 : ∀ p q : Fin 3, Normal ℤ 7 (basisInt 8 p*basisInt 13 q) := by decide
theorem products_row8 (b c : Fin 14) (h : Allowed 8 b c) (p q : Fin 3) : Normal ℤ c (basisInt 8 p*basisInt b q) := by
  fin_cases b <;> fin_cases c
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_8_1_1 p q
  · exact compatible_8_1_2 p q
  · exact compatible_8_1_3 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_8_1_6 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_8_2_2 p q
  · exact compatible_8_2_3 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_8_2_6 p q
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_8_2_8 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_8_3_3 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_8_6_8 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_8_7_7 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_8_8_8 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_8_9_8 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · exact compatible_8_13_7 p q
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
  · norm_num [Allowed,allowedTargets] at h
end UniserialComputations.N6
