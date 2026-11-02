import N6Constraints18
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
theorem image_18_0 (f : HomData π 18 0) : Normal k (homKind 18 0) (reduceHom π ρ f) := by
  have h00 := constraint_18_0_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_18_0_1_0 π ρ h6 ann f
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
theorem image_18_1 (f : HomData π 18 1) : Normal k (homKind 18 1) (reduceHom π ρ f) := by
  have h00 := constraint_18_1_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_2 (f : HomData π 18 2) : Normal k (homKind 18 2) (reduceHom π ρ f) := by
  have h00 := constraint_18_2_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_18_2_1_0 π ρ h6 ann f
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
theorem image_18_3 (f : HomData π 18 3) : Normal k (homKind 18 3) (reduceHom π ρ f) := by
  have h00 := constraint_18_3_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_4 (f : HomData π 18 4) : Normal k (homKind 18 4) (reduceHom π ρ f) := by
  have h00 := constraint_18_4_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_5 (f : HomData π 18 5) : Normal k (homKind 18 5) (reduceHom π ρ f) := by
  have h00 := constraint_18_5_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_6 (f : HomData π 18 6) : Normal k (homKind 18 6) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_7 (f : HomData π 18 7) : Normal k (homKind 18 7) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_8 (f : HomData π 18 8) : Normal k (homKind 18 8) (reduceHom π ρ f) := by
  have h00 := constraint_18_8_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_9 (f : HomData π 18 9) : Normal k (homKind 18 9) (reduceHom π ρ f) := by
  have h00 := constraint_18_9_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_10 (f : HomData π 18 10) : Normal k (homKind 18 10) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_11 (f : HomData π 18 11) : Normal k (homKind 18 11) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_12 (f : HomData π 18 12) : Normal k (homKind 18 12) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_13 (f : HomData π 18 13) : Normal k (homKind 18 13) (reduceHom π ρ f) := by
  have h00 := constraint_18_13_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_14 (f : HomData π 18 14) : Normal k (homKind 18 14) (reduceHom π ρ f) := by
  have h00 := constraint_18_14_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_15 (f : HomData π 18 15) : Normal k (homKind 18 15) (reduceHom π ρ f) := by
  have h00 := constraint_18_15_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_16 (f : HomData π 18 16) : Normal k (homKind 18 16) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_17 (f : HomData π 18 17) : Normal k (homKind 18 17) (reduceHom π ρ f) := by
  have h00 := constraint_18_17_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_18 (f : HomData π 18 18) : Normal k (homKind 18 18) (reduceHom π ρ f) := by
  have h01 := constraint_18_18_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_18_18_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 6 (reduceHom π ρ f)
  apply normal_form_6
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_18_19 (f : HomData π 18 19) : Normal k (homKind 18 19) (reduceHom π ρ f) := by
  have h00 := constraint_18_19_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_20 (f : HomData π 18 20) : Normal k (homKind 18 20) (reduceHom π ρ f) := by
  have h00 := constraint_18_20_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_21 (f : HomData π 18 21) : Normal k (homKind 18 21) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_22 (f : HomData π 18 22) : Normal k (homKind 18 22) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_23 (f : HomData π 18 23) : Normal k (homKind 18 23) (reduceHom π ρ f) := by
  have h00 := constraint_18_23_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_24 (f : HomData π 18 24) : Normal k (homKind 18 24) (reduceHom π ρ f) := by
  have h01 := constraint_18_24_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_18_24_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_18_25 (f : HomData π 18 25) : Normal k (homKind 18 25) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_26 (f : HomData π 18 26) : Normal k (homKind 18 26) (reduceHom π ρ f) := by
  have h01 := constraint_18_26_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_18_26_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 6 (reduceHom π ρ f)
  apply normal_form_6
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_18_27 (f : HomData π 18 27) : Normal k (homKind 18 27) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_28 (f : HomData π 18 28) : Normal k (homKind 18 28) (reduceHom π ρ f) := by
  have h00 := constraint_18_28_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_29 (f : HomData π 18 29) : Normal k (homKind 18 29) (reduceHom π ρ f) := by
  have h00 := constraint_18_29_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_30 (f : HomData π 18 30) : Normal k (homKind 18 30) (reduceHom π ρ f) := by
  have h01 := constraint_18_30_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 8 (reduceHom π ρ f)
  apply normal_form_8
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_18_31 (f : HomData π 18 31) : Normal k (homKind 18 31) (reduceHom π ρ f) := by
  have h01 := constraint_18_31_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 8 (reduceHom π ρ f)
  apply normal_form_8
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_18_32 (f : HomData π 18 32) : Normal k (homKind 18 32) (reduceHom π ρ f) := by
  have h01 := constraint_18_32_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 8 (reduceHom π ρ f)
  apply normal_form_8
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_18_33 (f : HomData π 18 33) : Normal k (homKind 18 33) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_34 (f : HomData π 18 34) : Normal k (homKind 18 34) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_35 (f : HomData π 18 35) : Normal k (homKind 18 35) (reduceHom π ρ f) := by
  have h00 := constraint_18_35_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_36 (f : HomData π 18 36) : Normal k (homKind 18 36) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_37 (f : HomData π 18 37) : Normal k (homKind 18 37) (reduceHom π ρ f) := by
  have h01 := constraint_18_37_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 8 (reduceHom π ρ f)
  apply normal_form_8
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_18_38 (f : HomData π 18 38) : Normal k (homKind 18 38) (reduceHom π ρ f) := by
  have h01 := constraint_18_38_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 8 (reduceHom π ρ f)
  apply normal_form_8
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_18_39 (f : HomData π 18 39) : Normal k (homKind 18 39) (reduceHom π ρ f) := by
  have h01 := constraint_18_39_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 8 (reduceHom π ρ f)
  apply normal_form_8
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_18_40 (f : HomData π 18 40) : Normal k (homKind 18 40) (reduceHom π ρ f) := by
  have h01 := constraint_18_40_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 8 (reduceHom π ρ f)
  apply normal_form_8
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_18_41 (f : HomData π 18 41) : Normal k (homKind 18 41) (reduceHom π ρ f) := by
  have h01 := constraint_18_41_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_18_41_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 6 (reduceHom π ρ f)
  apply normal_form_6
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_18_42 (f : HomData π 18 42) : Normal k (homKind 18 42) (reduceHom π ρ f) := by
  have h01 := constraint_18_42_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 8 (reduceHom π ρ f)
  apply normal_form_8
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_18_43 (f : HomData π 18 43) : Normal k (homKind 18 43) (reduceHom π ρ f) := by
  have h00 := constraint_18_43_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_18_43_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_18_44 (f : HomData π 18 44) : Normal k (homKind 18 44) (reduceHom π ρ f) := by
  have h01 := constraint_18_44_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 8 (reduceHom π ρ f)
  apply normal_form_8
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_18_45 (f : HomData π 18 45) : Normal k (homKind 18 45) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_18_46 (f : HomData π 18 46) : Normal k (homKind 18 46) (reduceHom π ρ f) := by
  have h00 := constraint_18_46_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_18_46_1_0 π ρ h6 ann f
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
theorem image_row18 (j : Fin 47) (f : HomData π 18 j) : Normal k (homKind 18 j) (reduceHom π ρ f) := by
  fin_cases j
  · exact image_18_0 π ρ h6 ann f
  · exact image_18_1 π ρ h6 ann f
  · exact image_18_2 π ρ h6 ann f
  · exact image_18_3 π ρ h6 ann f
  · exact image_18_4 π ρ h6 ann f
  · exact image_18_5 π ρ h6 ann f
  · exact image_18_6 π ρ h6 ann f
  · exact image_18_7 π ρ h6 ann f
  · exact image_18_8 π ρ h6 ann f
  · exact image_18_9 π ρ h6 ann f
  · exact image_18_10 π ρ h6 ann f
  · exact image_18_11 π ρ h6 ann f
  · exact image_18_12 π ρ h6 ann f
  · exact image_18_13 π ρ h6 ann f
  · exact image_18_14 π ρ h6 ann f
  · exact image_18_15 π ρ h6 ann f
  · exact image_18_16 π ρ h6 ann f
  · exact image_18_17 π ρ h6 ann f
  · exact image_18_18 π ρ h6 ann f
  · exact image_18_19 π ρ h6 ann f
  · exact image_18_20 π ρ h6 ann f
  · exact image_18_21 π ρ h6 ann f
  · exact image_18_22 π ρ h6 ann f
  · exact image_18_23 π ρ h6 ann f
  · exact image_18_24 π ρ h6 ann f
  · exact image_18_25 π ρ h6 ann f
  · exact image_18_26 π ρ h6 ann f
  · exact image_18_27 π ρ h6 ann f
  · exact image_18_28 π ρ h6 ann f
  · exact image_18_29 π ρ h6 ann f
  · exact image_18_30 π ρ h6 ann f
  · exact image_18_31 π ρ h6 ann f
  · exact image_18_32 π ρ h6 ann f
  · exact image_18_33 π ρ h6 ann f
  · exact image_18_34 π ρ h6 ann f
  · exact image_18_35 π ρ h6 ann f
  · exact image_18_36 π ρ h6 ann f
  · exact image_18_37 π ρ h6 ann f
  · exact image_18_38 π ρ h6 ann f
  · exact image_18_39 π ρ h6 ann f
  · exact image_18_40 π ρ h6 ann f
  · exact image_18_41 π ρ h6 ann f
  · exact image_18_42 π ρ h6 ann f
  · exact image_18_43 π ρ h6 ann f
  · exact image_18_44 π ρ h6 ann f
  · exact image_18_45 π ρ h6 ann f
  · exact image_18_46 π ρ h6 ann f
end UniserialComputations.N6
