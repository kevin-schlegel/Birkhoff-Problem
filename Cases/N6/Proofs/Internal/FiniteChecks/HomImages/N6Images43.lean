import N6Constraints43
import N6NormalForms
noncomputable section
namespace UniserialComputations.N6
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
variable {R k : Type*} [CommRing R] [Field k] (π : R) (ρ : R →+* k)
variable (h6 : π^6=0) (ann : ∀ r, π^5*r=0 ↔ ρ r=0)
include h6 ann in
theorem image_43_0 (f : HomData π 43 0) : Normal k (homKind 43 0) (reduceHom π ρ f) := by
  have h00 := constraint_43_0_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_0_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_1 (f : HomData π 43 1) : Normal k (homKind 43 1) (reduceHom π ρ f) := by
  have h00 := constraint_43_1_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_1_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_2 (f : HomData π 43 2) : Normal k (homKind 43 2) (reduceHom π ρ f) := by
  have h00 := constraint_43_2_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_2_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_3 (f : HomData π 43 3) : Normal k (homKind 43 3) (reduceHom π ρ f) := by
  have h00 := constraint_43_3_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_3_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_4 (f : HomData π 43 4) : Normal k (homKind 43 4) (reduceHom π ρ f) := by
  have h00 := constraint_43_4_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_4_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_5 (f : HomData π 43 5) : Normal k (homKind 43 5) (reduceHom π ρ f) := by
  have h00 := constraint_43_5_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_5_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_6 (f : HomData π 43 6) : Normal k (homKind 43 6) (reduceHom π ρ f) := by
  have h10 := constraint_43_6_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 4 (reduceHom π ρ f)
  apply normal_form_4
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_7 (f : HomData π 43 7) : Normal k (homKind 43 7) (reduceHom π ρ f) := by
  have h10 := constraint_43_7_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 4 (reduceHom π ρ f)
  apply normal_form_4
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_8 (f : HomData π 43 8) : Normal k (homKind 43 8) (reduceHom π ρ f) := by
  have h00 := constraint_43_8_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_8_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_9 (f : HomData π 43 9) : Normal k (homKind 43 9) (reduceHom π ρ f) := by
  have h00 := constraint_43_9_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_9_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_10 (f : HomData π 43 10) : Normal k (homKind 43 10) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_11 (f : HomData π 43 11) : Normal k (homKind 43 11) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_12 (f : HomData π 43 12) : Normal k (homKind 43 12) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_13 (f : HomData π 43 13) : Normal k (homKind 43 13) (reduceHom π ρ f) := by
  have h00 := constraint_43_13_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_14 (f : HomData π 43 14) : Normal k (homKind 43 14) (reduceHom π ρ f) := by
  have h00 := constraint_43_14_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_14_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_15 (f : HomData π 43 15) : Normal k (homKind 43 15) (reduceHom π ρ f) := by
  have h00 := constraint_43_15_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_15_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_16 (f : HomData π 43 16) : Normal k (homKind 43 16) (reduceHom π ρ f) := by
  have h10 := constraint_43_16_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 4 (reduceHom π ρ f)
  apply normal_form_4
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_17 (f : HomData π 43 17) : Normal k (homKind 43 17) (reduceHom π ρ f) := by
  have h00 := constraint_43_17_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_17_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_18 (f : HomData π 43 18) : Normal k (homKind 43 18) (reduceHom π ρ f) := by
  have h01 := constraint_43_18_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h10 := constraint_43_18_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  have h11 := constraint_43_18_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 4 (reduceHom π ρ f)
  apply normal_form_4
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_19 (f : HomData π 43 19) : Normal k (homKind 43 19) (reduceHom π ρ f) := by
  have h00 := constraint_43_19_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_19_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_20 (f : HomData π 43 20) : Normal k (homKind 43 20) (reduceHom π ρ f) := by
  have h00 := constraint_43_20_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_20_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_21 (f : HomData π 43 21) : Normal k (homKind 43 21) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_22 (f : HomData π 43 22) : Normal k (homKind 43 22) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_23 (f : HomData π 43 23) : Normal k (homKind 43 23) (reduceHom π ρ f) := by
  have h00 := constraint_43_23_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_23_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_24 (f : HomData π 43 24) : Normal k (homKind 43 24) (reduceHom π ρ f) := by
  have h01 := constraint_43_24_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_43_24_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_25 (f : HomData π 43 25) : Normal k (homKind 43 25) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_26 (f : HomData π 43 26) : Normal k (homKind 43 26) (reduceHom π ρ f) := by
  have h01 := constraint_43_26_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_43_26_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_27 (f : HomData π 43 27) : Normal k (homKind 43 27) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_28 (f : HomData π 43 28) : Normal k (homKind 43 28) (reduceHom π ρ f) := by
  have h10 := constraint_43_28_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_29 (f : HomData π 43 29) : Normal k (homKind 43 29) (reduceHom π ρ f) := by
  have h00 := constraint_43_29_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_29_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_30 (f : HomData π 43 30) : Normal k (homKind 43 30) (reduceHom π ρ f) := by
  have h01 := constraint_43_30_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_43_30_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_31 (f : HomData π 43 31) : Normal k (homKind 43 31) (reduceHom π ρ f) := by
  have h01 := constraint_43_31_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_43_31_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_32 (f : HomData π 43 32) : Normal k (homKind 43 32) (reduceHom π ρ f) := by
  have h01 := constraint_43_32_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_43_32_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_33 (f : HomData π 43 33) : Normal k (homKind 43 33) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_34 (f : HomData π 43 34) : Normal k (homKind 43 34) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_35 (f : HomData π 43 35) : Normal k (homKind 43 35) (reduceHom π ρ f) := by
  have h00 := constraint_43_35_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_36 (f : HomData π 43 36) : Normal k (homKind 43 36) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_37 (f : HomData π 43 37) : Normal k (homKind 43 37) (reduceHom π ρ f) := by
  have h01 := constraint_43_37_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_43_37_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_38 (f : HomData π 43 38) : Normal k (homKind 43 38) (reduceHom π ρ f) := by
  have h01 := constraint_43_38_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_43_38_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_39 (f : HomData π 43 39) : Normal k (homKind 43 39) (reduceHom π ρ f) := by
  have h01 := constraint_43_39_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_43_39_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_40 (f : HomData π 43 40) : Normal k (homKind 43 40) (reduceHom π ρ f) := by
  have h01 := constraint_43_40_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_43_40_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_41 (f : HomData π 43 41) : Normal k (homKind 43 41) (reduceHom π ρ f) := by
  have h01 := constraint_43_41_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_43_41_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_42 (f : HomData π 43 42) : Normal k (homKind 43 42) (reduceHom π ρ f) := by
  have h01 := constraint_43_42_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_43_42_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_43 (f : HomData π 43 43) : Normal k (homKind 43 43) (reduceHom π ρ f) := by
  have h01 := constraint_43_43_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h10 := constraint_43_43_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  have h11 := constraint_43_43_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 12 (reduceHom π ρ f)
  apply normal_form_12
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_44 (f : HomData π 43 44) : Normal k (homKind 43 44) (reduceHom π ρ f) := by
  have h01 := constraint_43_44_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_43_44_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_43_45 (f : HomData π 43 45) : Normal k (homKind 43 45) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_43_46 (f : HomData π 43 46) : Normal k (homKind 43 46) (reduceHom π ρ f) := by
  have h00 := constraint_43_46_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_43_46_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_row43 (j : Fin 47) (f : HomData π 43 j) : Normal k (homKind 43 j) (reduceHom π ρ f) := by
  fin_cases j
  · exact image_43_0 π ρ h6 ann f
  · exact image_43_1 π ρ h6 ann f
  · exact image_43_2 π ρ h6 ann f
  · exact image_43_3 π ρ h6 ann f
  · exact image_43_4 π ρ h6 ann f
  · exact image_43_5 π ρ h6 ann f
  · exact image_43_6 π ρ h6 ann f
  · exact image_43_7 π ρ h6 ann f
  · exact image_43_8 π ρ h6 ann f
  · exact image_43_9 π ρ h6 ann f
  · exact image_43_10 π ρ h6 ann f
  · exact image_43_11 π ρ h6 ann f
  · exact image_43_12 π ρ h6 ann f
  · exact image_43_13 π ρ h6 ann f
  · exact image_43_14 π ρ h6 ann f
  · exact image_43_15 π ρ h6 ann f
  · exact image_43_16 π ρ h6 ann f
  · exact image_43_17 π ρ h6 ann f
  · exact image_43_18 π ρ h6 ann f
  · exact image_43_19 π ρ h6 ann f
  · exact image_43_20 π ρ h6 ann f
  · exact image_43_21 π ρ h6 ann f
  · exact image_43_22 π ρ h6 ann f
  · exact image_43_23 π ρ h6 ann f
  · exact image_43_24 π ρ h6 ann f
  · exact image_43_25 π ρ h6 ann f
  · exact image_43_26 π ρ h6 ann f
  · exact image_43_27 π ρ h6 ann f
  · exact image_43_28 π ρ h6 ann f
  · exact image_43_29 π ρ h6 ann f
  · exact image_43_30 π ρ h6 ann f
  · exact image_43_31 π ρ h6 ann f
  · exact image_43_32 π ρ h6 ann f
  · exact image_43_33 π ρ h6 ann f
  · exact image_43_34 π ρ h6 ann f
  · exact image_43_35 π ρ h6 ann f
  · exact image_43_36 π ρ h6 ann f
  · exact image_43_37 π ρ h6 ann f
  · exact image_43_38 π ρ h6 ann f
  · exact image_43_39 π ρ h6 ann f
  · exact image_43_40 π ρ h6 ann f
  · exact image_43_41 π ρ h6 ann f
  · exact image_43_42 π ρ h6 ann f
  · exact image_43_43 π ρ h6 ann f
  · exact image_43_44 π ρ h6 ann f
  · exact image_43_45 π ρ h6 ann f
  · exact image_43_46 π ρ h6 ann f
end UniserialComputations.N6
