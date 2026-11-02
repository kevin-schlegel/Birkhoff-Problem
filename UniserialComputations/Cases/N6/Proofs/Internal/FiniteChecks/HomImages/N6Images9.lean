import N6Constraints9
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
theorem image_9_0 (f : HomData π 9 0) : Normal k (homKind 9 0) (reduceHom π ρ f) := by
  have h00 := constraint_9_0_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_1 (f : HomData π 9 1) : Normal k (homKind 9 1) (reduceHom π ρ f) := by
  have h00 := constraint_9_1_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_2 (f : HomData π 9 2) : Normal k (homKind 9 2) (reduceHom π ρ f) := by
  have h00 := constraint_9_2_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_3 (f : HomData π 9 3) : Normal k (homKind 9 3) (reduceHom π ρ f) := by
  have h00 := constraint_9_3_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_4 (f : HomData π 9 4) : Normal k (homKind 9 4) (reduceHom π ρ f) := by
  have h00 := constraint_9_4_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_5 (f : HomData π 9 5) : Normal k (homKind 9 5) (reduceHom π ρ f) := by
  have h00 := constraint_9_5_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_6 (f : HomData π 9 6) : Normal k (homKind 9 6) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_7 (f : HomData π 9 7) : Normal k (homKind 9 7) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_8 (f : HomData π 9 8) : Normal k (homKind 9 8) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_9 (f : HomData π 9 9) : Normal k (homKind 9 9) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_10 (f : HomData π 9 10) : Normal k (homKind 9 10) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_11 (f : HomData π 9 11) : Normal k (homKind 9 11) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_12 (f : HomData π 9 12) : Normal k (homKind 9 12) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_13 (f : HomData π 9 13) : Normal k (homKind 9 13) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_14 (f : HomData π 9 14) : Normal k (homKind 9 14) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_15 (f : HomData π 9 15) : Normal k (homKind 9 15) (reduceHom π ρ f) := by
  have h00 := constraint_9_15_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_16 (f : HomData π 9 16) : Normal k (homKind 9 16) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_17 (f : HomData π 9 17) : Normal k (homKind 9 17) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_18 (f : HomData π 9 18) : Normal k (homKind 9 18) (reduceHom π ρ f) := by
  have h01 := constraint_9_18_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_19 (f : HomData π 9 19) : Normal k (homKind 9 19) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_20 (f : HomData π 9 20) : Normal k (homKind 9 20) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_21 (f : HomData π 9 21) : Normal k (homKind 9 21) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_22 (f : HomData π 9 22) : Normal k (homKind 9 22) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_23 (f : HomData π 9 23) : Normal k (homKind 9 23) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_24 (f : HomData π 9 24) : Normal k (homKind 9 24) (reduceHom π ρ f) := by
  have h01 := constraint_9_24_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_25 (f : HomData π 9 25) : Normal k (homKind 9 25) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_26 (f : HomData π 9 26) : Normal k (homKind 9 26) (reduceHom π ρ f) := by
  have h01 := constraint_9_26_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_27 (f : HomData π 9 27) : Normal k (homKind 9 27) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_28 (f : HomData π 9 28) : Normal k (homKind 9 28) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_29 (f : HomData π 9 29) : Normal k (homKind 9 29) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_30 (f : HomData π 9 30) : Normal k (homKind 9 30) (reduceHom π ρ f) := by
  have h01 := constraint_9_30_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_31 (f : HomData π 9 31) : Normal k (homKind 9 31) (reduceHom π ρ f) := by
  have h01 := constraint_9_31_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_32 (f : HomData π 9 32) : Normal k (homKind 9 32) (reduceHom π ρ f) := by
  have h01 := constraint_9_32_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_33 (f : HomData π 9 33) : Normal k (homKind 9 33) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_34 (f : HomData π 9 34) : Normal k (homKind 9 34) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_35 (f : HomData π 9 35) : Normal k (homKind 9 35) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_36 (f : HomData π 9 36) : Normal k (homKind 9 36) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_37 (f : HomData π 9 37) : Normal k (homKind 9 37) (reduceHom π ρ f) := by
  have h01 := constraint_9_37_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_38 (f : HomData π 9 38) : Normal k (homKind 9 38) (reduceHom π ρ f) := by
  have h01 := constraint_9_38_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_39 (f : HomData π 9 39) : Normal k (homKind 9 39) (reduceHom π ρ f) := by
  have h01 := constraint_9_39_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_40 (f : HomData π 9 40) : Normal k (homKind 9 40) (reduceHom π ρ f) := by
  have h01 := constraint_9_40_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_41 (f : HomData π 9 41) : Normal k (homKind 9 41) (reduceHom π ρ f) := by
  have h01 := constraint_9_41_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_42 (f : HomData π 9 42) : Normal k (homKind 9 42) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_43 (f : HomData π 9 43) : Normal k (homKind 9 43) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_44 (f : HomData π 9 44) : Normal k (homKind 9 44) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_45 (f : HomData π 9 45) : Normal k (homKind 9 45) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_9_46 (f : HomData π 9 46) : Normal k (homKind 9 46) (reduceHom π ρ f) := by
  have h00 := constraint_9_46_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_row9 (j : Fin 47) (f : HomData π 9 j) : Normal k (homKind 9 j) (reduceHom π ρ f) := by
  fin_cases j
  · exact image_9_0 π ρ h6 ann f
  · exact image_9_1 π ρ h6 ann f
  · exact image_9_2 π ρ h6 ann f
  · exact image_9_3 π ρ h6 ann f
  · exact image_9_4 π ρ h6 ann f
  · exact image_9_5 π ρ h6 ann f
  · exact image_9_6 π ρ h6 ann f
  · exact image_9_7 π ρ h6 ann f
  · exact image_9_8 π ρ h6 ann f
  · exact image_9_9 π ρ h6 ann f
  · exact image_9_10 π ρ h6 ann f
  · exact image_9_11 π ρ h6 ann f
  · exact image_9_12 π ρ h6 ann f
  · exact image_9_13 π ρ h6 ann f
  · exact image_9_14 π ρ h6 ann f
  · exact image_9_15 π ρ h6 ann f
  · exact image_9_16 π ρ h6 ann f
  · exact image_9_17 π ρ h6 ann f
  · exact image_9_18 π ρ h6 ann f
  · exact image_9_19 π ρ h6 ann f
  · exact image_9_20 π ρ h6 ann f
  · exact image_9_21 π ρ h6 ann f
  · exact image_9_22 π ρ h6 ann f
  · exact image_9_23 π ρ h6 ann f
  · exact image_9_24 π ρ h6 ann f
  · exact image_9_25 π ρ h6 ann f
  · exact image_9_26 π ρ h6 ann f
  · exact image_9_27 π ρ h6 ann f
  · exact image_9_28 π ρ h6 ann f
  · exact image_9_29 π ρ h6 ann f
  · exact image_9_30 π ρ h6 ann f
  · exact image_9_31 π ρ h6 ann f
  · exact image_9_32 π ρ h6 ann f
  · exact image_9_33 π ρ h6 ann f
  · exact image_9_34 π ρ h6 ann f
  · exact image_9_35 π ρ h6 ann f
  · exact image_9_36 π ρ h6 ann f
  · exact image_9_37 π ρ h6 ann f
  · exact image_9_38 π ρ h6 ann f
  · exact image_9_39 π ρ h6 ann f
  · exact image_9_40 π ρ h6 ann f
  · exact image_9_41 π ρ h6 ann f
  · exact image_9_42 π ρ h6 ann f
  · exact image_9_43 π ρ h6 ann f
  · exact image_9_44 π ρ h6 ann f
  · exact image_9_45 π ρ h6 ann f
  · exact image_9_46 π ρ h6 ann f
end UniserialComputations.N6
