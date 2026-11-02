import N6Constraints24
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
theorem image_24_0 (f : HomData π 24 0) : Normal k (homKind 24 0) (reduceHom π ρ f) := by
  have h00 := constraint_24_0_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_24_0_1_0 π ρ h6 ann f
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
theorem image_24_1 (f : HomData π 24 1) : Normal k (homKind 24 1) (reduceHom π ρ f) := by
  have h00 := constraint_24_1_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_2 (f : HomData π 24 2) : Normal k (homKind 24 2) (reduceHom π ρ f) := by
  have h00 := constraint_24_2_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_24_2_1_0 π ρ h6 ann f
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
theorem image_24_3 (f : HomData π 24 3) : Normal k (homKind 24 3) (reduceHom π ρ f) := by
  have h00 := constraint_24_3_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_4 (f : HomData π 24 4) : Normal k (homKind 24 4) (reduceHom π ρ f) := by
  have h00 := constraint_24_4_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_5 (f : HomData π 24 5) : Normal k (homKind 24 5) (reduceHom π ρ f) := by
  have h00 := constraint_24_5_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_6 (f : HomData π 24 6) : Normal k (homKind 24 6) (reduceHom π ρ f) := by
  have h00 := constraint_24_6_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_7 (f : HomData π 24 7) : Normal k (homKind 24 7) (reduceHom π ρ f) := by
  have h00 := constraint_24_7_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_8 (f : HomData π 24 8) : Normal k (homKind 24 8) (reduceHom π ρ f) := by
  have h00 := constraint_24_8_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_9 (f : HomData π 24 9) : Normal k (homKind 24 9) (reduceHom π ρ f) := by
  have h00 := constraint_24_9_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_10 (f : HomData π 24 10) : Normal k (homKind 24 10) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_11 (f : HomData π 24 11) : Normal k (homKind 24 11) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_12 (f : HomData π 24 12) : Normal k (homKind 24 12) (reduceHom π ρ f) := by
  have h00 := constraint_24_12_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_13 (f : HomData π 24 13) : Normal k (homKind 24 13) (reduceHom π ρ f) := by
  have h00 := constraint_24_13_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_14 (f : HomData π 24 14) : Normal k (homKind 24 14) (reduceHom π ρ f) := by
  have h00 := constraint_24_14_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_15 (f : HomData π 24 15) : Normal k (homKind 24 15) (reduceHom π ρ f) := by
  have h00 := constraint_24_15_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_16 (f : HomData π 24 16) : Normal k (homKind 24 16) (reduceHom π ρ f) := by
  have h00 := constraint_24_16_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_17 (f : HomData π 24 17) : Normal k (homKind 24 17) (reduceHom π ρ f) := by
  have h00 := constraint_24_17_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_18 (f : HomData π 24 18) : Normal k (homKind 24 18) (reduceHom π ρ f) := by
  have h00 := constraint_24_18_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_24_18_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_24_19 (f : HomData π 24 19) : Normal k (homKind 24 19) (reduceHom π ρ f) := by
  have h00 := constraint_24_19_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_20 (f : HomData π 24 20) : Normal k (homKind 24 20) (reduceHom π ρ f) := by
  have h00 := constraint_24_20_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_21 (f : HomData π 24 21) : Normal k (homKind 24 21) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_22 (f : HomData π 24 22) : Normal k (homKind 24 22) (reduceHom π ρ f) := by
  have h00 := constraint_24_22_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_23 (f : HomData π 24 23) : Normal k (homKind 24 23) (reduceHom π ρ f) := by
  have h00 := constraint_24_23_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_24 (f : HomData π 24 24) : Normal k (homKind 24 24) (reduceHom π ρ f) := by
  have h01 := constraint_24_24_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  have h11 := constraint_24_24_1_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h11
  change Normal k 6 (reduceHom π ρ f)
  apply normal_form_6
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h11
include h6 ann in
theorem image_24_25 (f : HomData π 24 25) : Normal k (homKind 24 25) (reduceHom π ρ f) := by
  have h00 := constraint_24_25_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_26 (f : HomData π 24 26) : Normal k (homKind 24 26) (reduceHom π ρ f) := by
  have h00 := constraint_24_26_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_24_26_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_24_27 (f : HomData π 24 27) : Normal k (homKind 24 27) (reduceHom π ρ f) := by
  have h00 := constraint_24_27_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_28 (f : HomData π 24 28) : Normal k (homKind 24 28) (reduceHom π ρ f) := by
  have h00 := constraint_24_28_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_29 (f : HomData π 24 29) : Normal k (homKind 24 29) (reduceHom π ρ f) := by
  have h00 := constraint_24_29_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_30 (f : HomData π 24 30) : Normal k (homKind 24 30) (reduceHom π ρ f) := by
  have h00 := constraint_24_30_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_24_30_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_24_31 (f : HomData π 24 31) : Normal k (homKind 24 31) (reduceHom π ρ f) := by
  have h00 := constraint_24_31_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_24_31_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_24_32 (f : HomData π 24 32) : Normal k (homKind 24 32) (reduceHom π ρ f) := by
  have h00 := constraint_24_32_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_24_32_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_24_33 (f : HomData π 24 33) : Normal k (homKind 24 33) (reduceHom π ρ f) := by
  have h00 := constraint_24_33_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_34 (f : HomData π 24 34) : Normal k (homKind 24 34) (reduceHom π ρ f) := by
  have h00 := constraint_24_34_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_35 (f : HomData π 24 35) : Normal k (homKind 24 35) (reduceHom π ρ f) := by
  have h00 := constraint_24_35_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_36 (f : HomData π 24 36) : Normal k (homKind 24 36) (reduceHom π ρ f) := by
  have h00 := constraint_24_36_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 2 (reduceHom π ρ f)
  apply normal_form_2
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_37 (f : HomData π 24 37) : Normal k (homKind 24 37) (reduceHom π ρ f) := by
  have h00 := constraint_24_37_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_24_37_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_24_38 (f : HomData π 24 38) : Normal k (homKind 24 38) (reduceHom π ρ f) := by
  have h00 := constraint_24_38_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_24_38_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_24_39 (f : HomData π 24 39) : Normal k (homKind 24 39) (reduceHom π ρ f) := by
  have h00 := constraint_24_39_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_24_39_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_24_40 (f : HomData π 24 40) : Normal k (homKind 24 40) (reduceHom π ρ f) := by
  have h00 := constraint_24_40_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_24_40_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_24_41 (f : HomData π 24 41) : Normal k (homKind 24 41) (reduceHom π ρ f) := by
  have h00 := constraint_24_41_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_24_41_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_24_42 (f : HomData π 24 42) : Normal k (homKind 24 42) (reduceHom π ρ f) := by
  have h00 := constraint_24_42_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_24_42_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_24_43 (f : HomData π 24 43) : Normal k (homKind 24 43) (reduceHom π ρ f) := by
  have h00 := constraint_24_43_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_24_43_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_24_44 (f : HomData π 24 44) : Normal k (homKind 24 44) (reduceHom π ρ f) := by
  have h00 := constraint_24_44_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_24_44_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 7 (reduceHom π ρ f)
  apply normal_form_7
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
include h6 ann in
theorem image_24_45 (f : HomData π 24 45) : Normal k (homKind 24 45) (reduceHom π ρ f) := by
  change Normal k 3 (reduceHom π ρ f)
  apply normal_form_3
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_24_46 (f : HomData π 24 46) : Normal k (homKind 24 46) (reduceHom π ρ f) := by
  have h00 := constraint_24_46_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h10 := constraint_24_46_1_0 π ρ h6 ann f
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
theorem image_row24 (j : Fin 47) (f : HomData π 24 j) : Normal k (homKind 24 j) (reduceHom π ρ f) := by
  fin_cases j
  · exact image_24_0 π ρ h6 ann f
  · exact image_24_1 π ρ h6 ann f
  · exact image_24_2 π ρ h6 ann f
  · exact image_24_3 π ρ h6 ann f
  · exact image_24_4 π ρ h6 ann f
  · exact image_24_5 π ρ h6 ann f
  · exact image_24_6 π ρ h6 ann f
  · exact image_24_7 π ρ h6 ann f
  · exact image_24_8 π ρ h6 ann f
  · exact image_24_9 π ρ h6 ann f
  · exact image_24_10 π ρ h6 ann f
  · exact image_24_11 π ρ h6 ann f
  · exact image_24_12 π ρ h6 ann f
  · exact image_24_13 π ρ h6 ann f
  · exact image_24_14 π ρ h6 ann f
  · exact image_24_15 π ρ h6 ann f
  · exact image_24_16 π ρ h6 ann f
  · exact image_24_17 π ρ h6 ann f
  · exact image_24_18 π ρ h6 ann f
  · exact image_24_19 π ρ h6 ann f
  · exact image_24_20 π ρ h6 ann f
  · exact image_24_21 π ρ h6 ann f
  · exact image_24_22 π ρ h6 ann f
  · exact image_24_23 π ρ h6 ann f
  · exact image_24_24 π ρ h6 ann f
  · exact image_24_25 π ρ h6 ann f
  · exact image_24_26 π ρ h6 ann f
  · exact image_24_27 π ρ h6 ann f
  · exact image_24_28 π ρ h6 ann f
  · exact image_24_29 π ρ h6 ann f
  · exact image_24_30 π ρ h6 ann f
  · exact image_24_31 π ρ h6 ann f
  · exact image_24_32 π ρ h6 ann f
  · exact image_24_33 π ρ h6 ann f
  · exact image_24_34 π ρ h6 ann f
  · exact image_24_35 π ρ h6 ann f
  · exact image_24_36 π ρ h6 ann f
  · exact image_24_37 π ρ h6 ann f
  · exact image_24_38 π ρ h6 ann f
  · exact image_24_39 π ρ h6 ann f
  · exact image_24_40 π ρ h6 ann f
  · exact image_24_41 π ρ h6 ann f
  · exact image_24_42 π ρ h6 ann f
  · exact image_24_43 π ρ h6 ann f
  · exact image_24_44 π ρ h6 ann f
  · exact image_24_45 π ρ h6 ann f
  · exact image_24_46 π ρ h6 ann f
end UniserialComputations.N6
