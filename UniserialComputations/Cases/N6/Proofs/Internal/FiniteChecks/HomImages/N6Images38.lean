import N6Constraints38
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
theorem image_38_0 (f : HomData π 38 0) : Normal k (homKind 38 0) (reduceHom π ρ f) := by
  have h00 := constraint_38_0_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_38_0_1_0 π ρ h6 ann f
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
theorem image_38_1 (f : HomData π 38 1) : Normal k (homKind 38 1) (reduceHom π ρ f) := by
  have h00 := constraint_38_1_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_38_1_1_0 π ρ h6 ann f
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
theorem image_38_2 (f : HomData π 38 2) : Normal k (homKind 38 2) (reduceHom π ρ f) := by
  have h00 := constraint_38_2_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_38_2_1_0 π ρ h6 ann f
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
theorem image_38_3 (f : HomData π 38 3) : Normal k (homKind 38 3) (reduceHom π ρ f) := by
  have h00 := constraint_38_3_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_4 (f : HomData π 38 4) : Normal k (homKind 38 4) (reduceHom π ρ f) := by
  have h00 := constraint_38_4_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_5 (f : HomData π 38 5) : Normal k (homKind 38 5) (reduceHom π ρ f) := by
  have h00 := constraint_38_5_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_38_5_1_0 π ρ h6 ann f
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
theorem image_38_6 (f : HomData π 38 6) : Normal k (homKind 38 6) (reduceHom π ρ f) := by
  have h00 := constraint_38_6_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_7 (f : HomData π 38 7) : Normal k (homKind 38 7) (reduceHom π ρ f) := by
  have h00 := constraint_38_7_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_8 (f : HomData π 38 8) : Normal k (homKind 38 8) (reduceHom π ρ f) := by
  have h00 := constraint_38_8_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_9 (f : HomData π 38 9) : Normal k (homKind 38 9) (reduceHom π ρ f) := by
  have h00 := constraint_38_9_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_38_9_1_0 π ρ h6 ann f
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
theorem image_38_10 (f : HomData π 38 10) : Normal k (homKind 38 10) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_11 (f : HomData π 38 11) : Normal k (homKind 38 11) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_12 (f : HomData π 38 12) : Normal k (homKind 38 12) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_13 (f : HomData π 38 13) : Normal k (homKind 38 13) (reduceHom π ρ f) := by
  have h00 := constraint_38_13_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_14 (f : HomData π 38 14) : Normal k (homKind 38 14) (reduceHom π ρ f) := by
  have h00 := constraint_38_14_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_38_14_1_0 π ρ h6 ann f
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
theorem image_38_15 (f : HomData π 38 15) : Normal k (homKind 38 15) (reduceHom π ρ f) := by
  have h00 := constraint_38_15_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_38_15_1_0 π ρ h6 ann f
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
theorem image_38_16 (f : HomData π 38 16) : Normal k (homKind 38 16) (reduceHom π ρ f) := by
  have h00 := constraint_38_16_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_17 (f : HomData π 38 17) : Normal k (homKind 38 17) (reduceHom π ρ f) := by
  have h00 := constraint_38_17_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_18 (f : HomData π 38 18) : Normal k (homKind 38 18) (reduceHom π ρ f) := by
  have h00 := constraint_38_18_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_38_18_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_38_18_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_38_19 (f : HomData π 38 19) : Normal k (homKind 38 19) (reduceHom π ρ f) := by
  have h00 := constraint_38_19_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_20 (f : HomData π 38 20) : Normal k (homKind 38 20) (reduceHom π ρ f) := by
  have h00 := constraint_38_20_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_21 (f : HomData π 38 21) : Normal k (homKind 38 21) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_22 (f : HomData π 38 22) : Normal k (homKind 38 22) (reduceHom π ρ f) := by
  have h00 := constraint_38_22_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_23 (f : HomData π 38 23) : Normal k (homKind 38 23) (reduceHom π ρ f) := by
  have h00 := constraint_38_23_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_24 (f : HomData π 38 24) : Normal k (homKind 38 24) (reduceHom π ρ f) := by
  have h01 := constraint_38_24_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_38_24_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_38_25 (f : HomData π 38 25) : Normal k (homKind 38 25) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_26 (f : HomData π 38 26) : Normal k (homKind 38 26) (reduceHom π ρ f) := by
  have h00 := constraint_38_26_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_38_26_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_38_26_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_38_27 (f : HomData π 38 27) : Normal k (homKind 38 27) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_28 (f : HomData π 38 28) : Normal k (homKind 38 28) (reduceHom π ρ f) := by
  have h00 := constraint_38_28_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_29 (f : HomData π 38 29) : Normal k (homKind 38 29) (reduceHom π ρ f) := by
  have h00 := constraint_38_29_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_30 (f : HomData π 38 30) : Normal k (homKind 38 30) (reduceHom π ρ f) := by
  have h01 := constraint_38_30_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 8 (reduceHom π ρ f)
  apply normal_form_8
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_38_31 (f : HomData π 38 31) : Normal k (homKind 38 31) (reduceHom π ρ f) := by
  have h00 := constraint_38_31_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_38_31_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_38_31_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_38_32 (f : HomData π 38 32) : Normal k (homKind 38 32) (reduceHom π ρ f) := by
  have h00 := constraint_38_32_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_38_32_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_38_32_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_38_33 (f : HomData π 38 33) : Normal k (homKind 38 33) (reduceHom π ρ f) := by
  have h00 := constraint_38_33_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_34 (f : HomData π 38 34) : Normal k (homKind 38 34) (reduceHom π ρ f) := by
  have h00 := constraint_38_34_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_35 (f : HomData π 38 35) : Normal k (homKind 38 35) (reduceHom π ρ f) := by
  have h00 := constraint_38_35_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_36 (f : HomData π 38 36) : Normal k (homKind 38 36) (reduceHom π ρ f) := by
  have h00 := constraint_38_36_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_37 (f : HomData π 38 37) : Normal k (homKind 38 37) (reduceHom π ρ f) := by
  have h01 := constraint_38_37_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_38_37_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 6 (reduceHom π ρ f)
  apply normal_form_6
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_38_38 (f : HomData π 38 38) : Normal k (homKind 38 38) (reduceHom π ρ f) := by
  have h01 := constraint_38_38_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_38_38_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 6 (reduceHom π ρ f)
  apply normal_form_6
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_38_39 (f : HomData π 38 39) : Normal k (homKind 38 39) (reduceHom π ρ f) := by
  have h00 := constraint_38_39_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_38_39_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_38_39_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_38_40 (f : HomData π 38 40) : Normal k (homKind 38 40) (reduceHom π ρ f) := by
  have h01 := constraint_38_40_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 8 (reduceHom π ρ f)
  apply normal_form_8
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_38_41 (f : HomData π 38 41) : Normal k (homKind 38 41) (reduceHom π ρ f) := by
  have h00 := constraint_38_41_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_38_41_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_38_41_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_38_42 (f : HomData π 38 42) : Normal k (homKind 38 42) (reduceHom π ρ f) := by
  have h01 := constraint_38_42_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 8 (reduceHom π ρ f)
  apply normal_form_8
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_38_43 (f : HomData π 38 43) : Normal k (homKind 38 43) (reduceHom π ρ f) := by
  have h00 := constraint_38_43_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_38_43_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_38_44 (f : HomData π 38 44) : Normal k (homKind 38 44) (reduceHom π ρ f) := by
  have h01 := constraint_38_44_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 8 (reduceHom π ρ f)
  apply normal_form_8
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_38_45 (f : HomData π 38 45) : Normal k (homKind 38 45) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_38_46 (f : HomData π 38 46) : Normal k (homKind 38 46) (reduceHom π ρ f) := by
  have h00 := constraint_38_46_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_38_46_1_0 π ρ h6 ann f
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
theorem image_row38 (j : Fin 47) (f : HomData π 38 j) : Normal k (homKind 38 j) (reduceHom π ρ f) := by
  fin_cases j
  · exact image_38_0 π ρ h6 ann f
  · exact image_38_1 π ρ h6 ann f
  · exact image_38_2 π ρ h6 ann f
  · exact image_38_3 π ρ h6 ann f
  · exact image_38_4 π ρ h6 ann f
  · exact image_38_5 π ρ h6 ann f
  · exact image_38_6 π ρ h6 ann f
  · exact image_38_7 π ρ h6 ann f
  · exact image_38_8 π ρ h6 ann f
  · exact image_38_9 π ρ h6 ann f
  · exact image_38_10 π ρ h6 ann f
  · exact image_38_11 π ρ h6 ann f
  · exact image_38_12 π ρ h6 ann f
  · exact image_38_13 π ρ h6 ann f
  · exact image_38_14 π ρ h6 ann f
  · exact image_38_15 π ρ h6 ann f
  · exact image_38_16 π ρ h6 ann f
  · exact image_38_17 π ρ h6 ann f
  · exact image_38_18 π ρ h6 ann f
  · exact image_38_19 π ρ h6 ann f
  · exact image_38_20 π ρ h6 ann f
  · exact image_38_21 π ρ h6 ann f
  · exact image_38_22 π ρ h6 ann f
  · exact image_38_23 π ρ h6 ann f
  · exact image_38_24 π ρ h6 ann f
  · exact image_38_25 π ρ h6 ann f
  · exact image_38_26 π ρ h6 ann f
  · exact image_38_27 π ρ h6 ann f
  · exact image_38_28 π ρ h6 ann f
  · exact image_38_29 π ρ h6 ann f
  · exact image_38_30 π ρ h6 ann f
  · exact image_38_31 π ρ h6 ann f
  · exact image_38_32 π ρ h6 ann f
  · exact image_38_33 π ρ h6 ann f
  · exact image_38_34 π ρ h6 ann f
  · exact image_38_35 π ρ h6 ann f
  · exact image_38_36 π ρ h6 ann f
  · exact image_38_37 π ρ h6 ann f
  · exact image_38_38 π ρ h6 ann f
  · exact image_38_39 π ρ h6 ann f
  · exact image_38_40 π ρ h6 ann f
  · exact image_38_41 π ρ h6 ann f
  · exact image_38_42 π ρ h6 ann f
  · exact image_38_43 π ρ h6 ann f
  · exact image_38_44 π ρ h6 ann f
  · exact image_38_45 π ρ h6 ann f
  · exact image_38_46 π ρ h6 ann f
end UniserialComputations.N6
