import N6Constraints44
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
theorem image_44_0 (f : HomData π 44 0) : Normal k (homKind 44 0) (reduceHom π ρ f) := by
  have h00 := constraint_44_0_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_0_1_0 π ρ h6 ann f
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
theorem image_44_1 (f : HomData π 44 1) : Normal k (homKind 44 1) (reduceHom π ρ f) := by
  have h00 := constraint_44_1_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_1_1_0 π ρ h6 ann f
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
theorem image_44_2 (f : HomData π 44 2) : Normal k (homKind 44 2) (reduceHom π ρ f) := by
  have h00 := constraint_44_2_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_2_1_0 π ρ h6 ann f
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
theorem image_44_3 (f : HomData π 44 3) : Normal k (homKind 44 3) (reduceHom π ρ f) := by
  have h00 := constraint_44_3_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_3_1_0 π ρ h6 ann f
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
theorem image_44_4 (f : HomData π 44 4) : Normal k (homKind 44 4) (reduceHom π ρ f) := by
  have h00 := constraint_44_4_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_4_1_0 π ρ h6 ann f
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
theorem image_44_5 (f : HomData π 44 5) : Normal k (homKind 44 5) (reduceHom π ρ f) := by
  have h00 := constraint_44_5_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_5_1_0 π ρ h6 ann f
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
theorem image_44_6 (f : HomData π 44 6) : Normal k (homKind 44 6) (reduceHom π ρ f) := by
  have h00 := constraint_44_6_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_6_1_0 π ρ h6 ann f
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
theorem image_44_7 (f : HomData π 44 7) : Normal k (homKind 44 7) (reduceHom π ρ f) := by
  have h00 := constraint_44_7_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_7_1_0 π ρ h6 ann f
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
theorem image_44_8 (f : HomData π 44 8) : Normal k (homKind 44 8) (reduceHom π ρ f) := by
  have h00 := constraint_44_8_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_8_1_0 π ρ h6 ann f
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
theorem image_44_9 (f : HomData π 44 9) : Normal k (homKind 44 9) (reduceHom π ρ f) := by
  have h00 := constraint_44_9_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_9_1_0 π ρ h6 ann f
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
theorem image_44_10 (f : HomData π 44 10) : Normal k (homKind 44 10) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_11 (f : HomData π 44 11) : Normal k (homKind 44 11) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_12 (f : HomData π 44 12) : Normal k (homKind 44 12) (reduceHom π ρ f) := by
  have h00 := constraint_44_12_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_13 (f : HomData π 44 13) : Normal k (homKind 44 13) (reduceHom π ρ f) := by
  have h00 := constraint_44_13_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_14 (f : HomData π 44 14) : Normal k (homKind 44 14) (reduceHom π ρ f) := by
  have h00 := constraint_44_14_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_14_1_0 π ρ h6 ann f
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
theorem image_44_15 (f : HomData π 44 15) : Normal k (homKind 44 15) (reduceHom π ρ f) := by
  have h00 := constraint_44_15_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_15_1_0 π ρ h6 ann f
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
theorem image_44_16 (f : HomData π 44 16) : Normal k (homKind 44 16) (reduceHom π ρ f) := by
  have h00 := constraint_44_16_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_16_1_0 π ρ h6 ann f
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
theorem image_44_17 (f : HomData π 44 17) : Normal k (homKind 44 17) (reduceHom π ρ f) := by
  have h00 := constraint_44_17_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_17_1_0 π ρ h6 ann f
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
theorem image_44_18 (f : HomData π 44 18) : Normal k (homKind 44 18) (reduceHom π ρ f) := by
  have h00 := constraint_44_18_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_44_18_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h10 := constraint_44_18_1_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h10
  have h11 := constraint_44_18_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h10
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_44_19 (f : HomData π 44 19) : Normal k (homKind 44 19) (reduceHom π ρ f) := by
  have h00 := constraint_44_19_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_19_1_0 π ρ h6 ann f
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
theorem image_44_20 (f : HomData π 44 20) : Normal k (homKind 44 20) (reduceHom π ρ f) := by
  have h00 := constraint_44_20_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_20_1_0 π ρ h6 ann f
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
theorem image_44_21 (f : HomData π 44 21) : Normal k (homKind 44 21) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_22 (f : HomData π 44 22) : Normal k (homKind 44 22) (reduceHom π ρ f) := by
  have h00 := constraint_44_22_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_23 (f : HomData π 44 23) : Normal k (homKind 44 23) (reduceHom π ρ f) := by
  have h00 := constraint_44_23_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_23_1_0 π ρ h6 ann f
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
theorem image_44_24 (f : HomData π 44 24) : Normal k (homKind 44 24) (reduceHom π ρ f) := by
  have h01 := constraint_44_24_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_44_24_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_44_25 (f : HomData π 44 25) : Normal k (homKind 44 25) (reduceHom π ρ f) := by
  have h00 := constraint_44_25_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_26 (f : HomData π 44 26) : Normal k (homKind 44 26) (reduceHom π ρ f) := by
  have h00 := constraint_44_26_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_44_26_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_44_26_1_1 π ρ h6 ann f
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
theorem image_44_27 (f : HomData π 44 27) : Normal k (homKind 44 27) (reduceHom π ρ f) := by
  have h00 := constraint_44_27_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_28 (f : HomData π 44 28) : Normal k (homKind 44 28) (reduceHom π ρ f) := by
  have h00 := constraint_44_28_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_29 (f : HomData π 44 29) : Normal k (homKind 44 29) (reduceHom π ρ f) := by
  have h00 := constraint_44_29_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_29_1_0 π ρ h6 ann f
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
theorem image_44_30 (f : HomData π 44 30) : Normal k (homKind 44 30) (reduceHom π ρ f) := by
  have h00 := constraint_44_30_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_44_30_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_44_30_1_1 π ρ h6 ann f
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
theorem image_44_31 (f : HomData π 44 31) : Normal k (homKind 44 31) (reduceHom π ρ f) := by
  have h00 := constraint_44_31_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_44_31_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_44_31_1_1 π ρ h6 ann f
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
theorem image_44_32 (f : HomData π 44 32) : Normal k (homKind 44 32) (reduceHom π ρ f) := by
  have h00 := constraint_44_32_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_44_32_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_44_32_1_1 π ρ h6 ann f
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
theorem image_44_33 (f : HomData π 44 33) : Normal k (homKind 44 33) (reduceHom π ρ f) := by
  have h00 := constraint_44_33_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_34 (f : HomData π 44 34) : Normal k (homKind 44 34) (reduceHom π ρ f) := by
  have h00 := constraint_44_34_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_35 (f : HomData π 44 35) : Normal k (homKind 44 35) (reduceHom π ρ f) := by
  have h00 := constraint_44_35_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_36 (f : HomData π 44 36) : Normal k (homKind 44 36) (reduceHom π ρ f) := by
  have h00 := constraint_44_36_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_37 (f : HomData π 44 37) : Normal k (homKind 44 37) (reduceHom π ρ f) := by
  have h00 := constraint_44_37_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_44_37_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_44_37_1_1 π ρ h6 ann f
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
theorem image_44_38 (f : HomData π 44 38) : Normal k (homKind 44 38) (reduceHom π ρ f) := by
  have h00 := constraint_44_38_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_44_38_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_44_38_1_1 π ρ h6 ann f
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
theorem image_44_39 (f : HomData π 44 39) : Normal k (homKind 44 39) (reduceHom π ρ f) := by
  have h00 := constraint_44_39_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_44_39_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_44_39_1_1 π ρ h6 ann f
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
theorem image_44_40 (f : HomData π 44 40) : Normal k (homKind 44 40) (reduceHom π ρ f) := by
  have h00 := constraint_44_40_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_44_40_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_44_40_1_1 π ρ h6 ann f
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
theorem image_44_41 (f : HomData π 44 41) : Normal k (homKind 44 41) (reduceHom π ρ f) := by
  have h00 := constraint_44_41_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_44_41_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_44_41_1_1 π ρ h6 ann f
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
theorem image_44_42 (f : HomData π 44 42) : Normal k (homKind 44 42) (reduceHom π ρ f) := by
  have h00 := constraint_44_42_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_44_42_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_44_42_1_1 π ρ h6 ann f
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
theorem image_44_43 (f : HomData π 44 43) : Normal k (homKind 44 43) (reduceHom π ρ f) := by
  have h00 := constraint_44_43_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_44_43_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_44_43_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 13 (reduceHom π ρ f)
  apply normal_form_13
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_44_44 (f : HomData π 44 44) : Normal k (homKind 44 44) (reduceHom π ρ f) := by
  have h01 := constraint_44_44_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_44_44_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 6 (reduceHom π ρ f)
  apply normal_form_6
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_44_45 (f : HomData π 44 45) : Normal k (homKind 44 45) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_44_46 (f : HomData π 44 46) : Normal k (homKind 44 46) (reduceHom π ρ f) := by
  have h00 := constraint_44_46_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_44_46_1_0 π ρ h6 ann f
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
theorem image_row44 (j : Fin 47) (f : HomData π 44 j) : Normal k (homKind 44 j) (reduceHom π ρ f) := by
  fin_cases j
  · exact image_44_0 π ρ h6 ann f
  · exact image_44_1 π ρ h6 ann f
  · exact image_44_2 π ρ h6 ann f
  · exact image_44_3 π ρ h6 ann f
  · exact image_44_4 π ρ h6 ann f
  · exact image_44_5 π ρ h6 ann f
  · exact image_44_6 π ρ h6 ann f
  · exact image_44_7 π ρ h6 ann f
  · exact image_44_8 π ρ h6 ann f
  · exact image_44_9 π ρ h6 ann f
  · exact image_44_10 π ρ h6 ann f
  · exact image_44_11 π ρ h6 ann f
  · exact image_44_12 π ρ h6 ann f
  · exact image_44_13 π ρ h6 ann f
  · exact image_44_14 π ρ h6 ann f
  · exact image_44_15 π ρ h6 ann f
  · exact image_44_16 π ρ h6 ann f
  · exact image_44_17 π ρ h6 ann f
  · exact image_44_18 π ρ h6 ann f
  · exact image_44_19 π ρ h6 ann f
  · exact image_44_20 π ρ h6 ann f
  · exact image_44_21 π ρ h6 ann f
  · exact image_44_22 π ρ h6 ann f
  · exact image_44_23 π ρ h6 ann f
  · exact image_44_24 π ρ h6 ann f
  · exact image_44_25 π ρ h6 ann f
  · exact image_44_26 π ρ h6 ann f
  · exact image_44_27 π ρ h6 ann f
  · exact image_44_28 π ρ h6 ann f
  · exact image_44_29 π ρ h6 ann f
  · exact image_44_30 π ρ h6 ann f
  · exact image_44_31 π ρ h6 ann f
  · exact image_44_32 π ρ h6 ann f
  · exact image_44_33 π ρ h6 ann f
  · exact image_44_34 π ρ h6 ann f
  · exact image_44_35 π ρ h6 ann f
  · exact image_44_36 π ρ h6 ann f
  · exact image_44_37 π ρ h6 ann f
  · exact image_44_38 π ρ h6 ann f
  · exact image_44_39 π ρ h6 ann f
  · exact image_44_40 π ρ h6 ann f
  · exact image_44_41 π ρ h6 ann f
  · exact image_44_42 π ρ h6 ann f
  · exact image_44_43 π ρ h6 ann f
  · exact image_44_44 π ρ h6 ann f
  · exact image_44_45 π ρ h6 ann f
  · exact image_44_46 π ρ h6 ann f
end UniserialComputations.N6
