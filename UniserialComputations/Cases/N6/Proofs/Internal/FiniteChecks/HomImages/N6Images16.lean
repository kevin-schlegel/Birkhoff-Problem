import N6Constraints16
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
theorem image_16_0 (f : HomData π 16 0) : Normal k (homKind 16 0) (reduceHom π ρ f) := by
  have h00 := constraint_16_0_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_1 (f : HomData π 16 1) : Normal k (homKind 16 1) (reduceHom π ρ f) := by
  have h00 := constraint_16_1_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_2 (f : HomData π 16 2) : Normal k (homKind 16 2) (reduceHom π ρ f) := by
  have h00 := constraint_16_2_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_3 (f : HomData π 16 3) : Normal k (homKind 16 3) (reduceHom π ρ f) := by
  have h00 := constraint_16_3_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_4 (f : HomData π 16 4) : Normal k (homKind 16 4) (reduceHom π ρ f) := by
  have h00 := constraint_16_4_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_5 (f : HomData π 16 5) : Normal k (homKind 16 5) (reduceHom π ρ f) := by
  have h00 := constraint_16_5_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_6 (f : HomData π 16 6) : Normal k (homKind 16 6) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_7 (f : HomData π 16 7) : Normal k (homKind 16 7) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_8 (f : HomData π 16 8) : Normal k (homKind 16 8) (reduceHom π ρ f) := by
  have h00 := constraint_16_8_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_9 (f : HomData π 16 9) : Normal k (homKind 16 9) (reduceHom π ρ f) := by
  have h00 := constraint_16_9_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_10 (f : HomData π 16 10) : Normal k (homKind 16 10) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_11 (f : HomData π 16 11) : Normal k (homKind 16 11) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_12 (f : HomData π 16 12) : Normal k (homKind 16 12) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_13 (f : HomData π 16 13) : Normal k (homKind 16 13) (reduceHom π ρ f) := by
  have h00 := constraint_16_13_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_14 (f : HomData π 16 14) : Normal k (homKind 16 14) (reduceHom π ρ f) := by
  have h00 := constraint_16_14_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_15 (f : HomData π 16 15) : Normal k (homKind 16 15) (reduceHom π ρ f) := by
  have h00 := constraint_16_15_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_16 (f : HomData π 16 16) : Normal k (homKind 16 16) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_17 (f : HomData π 16 17) : Normal k (homKind 16 17) (reduceHom π ρ f) := by
  have h00 := constraint_16_17_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_18 (f : HomData π 16 18) : Normal k (homKind 16 18) (reduceHom π ρ f) := by
  have h00 := constraint_16_18_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_16_18_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_19 (f : HomData π 16 19) : Normal k (homKind 16 19) (reduceHom π ρ f) := by
  have h00 := constraint_16_19_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_20 (f : HomData π 16 20) : Normal k (homKind 16 20) (reduceHom π ρ f) := by
  have h00 := constraint_16_20_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_21 (f : HomData π 16 21) : Normal k (homKind 16 21) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_22 (f : HomData π 16 22) : Normal k (homKind 16 22) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_23 (f : HomData π 16 23) : Normal k (homKind 16 23) (reduceHom π ρ f) := by
  have h00 := constraint_16_23_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_24 (f : HomData π 16 24) : Normal k (homKind 16 24) (reduceHom π ρ f) := by
  have h01 := constraint_16_24_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_25 (f : HomData π 16 25) : Normal k (homKind 16 25) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_26 (f : HomData π 16 26) : Normal k (homKind 16 26) (reduceHom π ρ f) := by
  have h00 := constraint_16_26_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_16_26_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_27 (f : HomData π 16 27) : Normal k (homKind 16 27) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_28 (f : HomData π 16 28) : Normal k (homKind 16 28) (reduceHom π ρ f) := by
  have h00 := constraint_16_28_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_29 (f : HomData π 16 29) : Normal k (homKind 16 29) (reduceHom π ρ f) := by
  have h00 := constraint_16_29_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_30 (f : HomData π 16 30) : Normal k (homKind 16 30) (reduceHom π ρ f) := by
  have h01 := constraint_16_30_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_31 (f : HomData π 16 31) : Normal k (homKind 16 31) (reduceHom π ρ f) := by
  have h01 := constraint_16_31_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_32 (f : HomData π 16 32) : Normal k (homKind 16 32) (reduceHom π ρ f) := by
  have h01 := constraint_16_32_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_33 (f : HomData π 16 33) : Normal k (homKind 16 33) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_34 (f : HomData π 16 34) : Normal k (homKind 16 34) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_35 (f : HomData π 16 35) : Normal k (homKind 16 35) (reduceHom π ρ f) := by
  have h00 := constraint_16_35_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_36 (f : HomData π 16 36) : Normal k (homKind 16 36) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_37 (f : HomData π 16 37) : Normal k (homKind 16 37) (reduceHom π ρ f) := by
  have h01 := constraint_16_37_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_38 (f : HomData π 16 38) : Normal k (homKind 16 38) (reduceHom π ρ f) := by
  have h01 := constraint_16_38_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_39 (f : HomData π 16 39) : Normal k (homKind 16 39) (reduceHom π ρ f) := by
  have h01 := constraint_16_39_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_40 (f : HomData π 16 40) : Normal k (homKind 16 40) (reduceHom π ρ f) := by
  have h01 := constraint_16_40_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_41 (f : HomData π 16 41) : Normal k (homKind 16 41) (reduceHom π ρ f) := by
  have h00 := constraint_16_41_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_16_41_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_42 (f : HomData π 16 42) : Normal k (homKind 16 42) (reduceHom π ρ f) := by
  have h01 := constraint_16_42_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_43 (f : HomData π 16 43) : Normal k (homKind 16 43) (reduceHom π ρ f) := by
  have h00 := constraint_16_43_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_16_43_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_44 (f : HomData π 16 44) : Normal k (homKind 16 44) (reduceHom π ρ f) := by
  have h01 := constraint_16_44_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_45 (f : HomData π 16 45) : Normal k (homKind 16 45) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_16_46 (f : HomData π 16 46) : Normal k (homKind 16 46) (reduceHom π ρ f) := by
  have h00 := constraint_16_46_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_row16 (j : Fin 47) (f : HomData π 16 j) : Normal k (homKind 16 j) (reduceHom π ρ f) := by
  fin_cases j
  · exact image_16_0 π ρ h6 ann f
  · exact image_16_1 π ρ h6 ann f
  · exact image_16_2 π ρ h6 ann f
  · exact image_16_3 π ρ h6 ann f
  · exact image_16_4 π ρ h6 ann f
  · exact image_16_5 π ρ h6 ann f
  · exact image_16_6 π ρ h6 ann f
  · exact image_16_7 π ρ h6 ann f
  · exact image_16_8 π ρ h6 ann f
  · exact image_16_9 π ρ h6 ann f
  · exact image_16_10 π ρ h6 ann f
  · exact image_16_11 π ρ h6 ann f
  · exact image_16_12 π ρ h6 ann f
  · exact image_16_13 π ρ h6 ann f
  · exact image_16_14 π ρ h6 ann f
  · exact image_16_15 π ρ h6 ann f
  · exact image_16_16 π ρ h6 ann f
  · exact image_16_17 π ρ h6 ann f
  · exact image_16_18 π ρ h6 ann f
  · exact image_16_19 π ρ h6 ann f
  · exact image_16_20 π ρ h6 ann f
  · exact image_16_21 π ρ h6 ann f
  · exact image_16_22 π ρ h6 ann f
  · exact image_16_23 π ρ h6 ann f
  · exact image_16_24 π ρ h6 ann f
  · exact image_16_25 π ρ h6 ann f
  · exact image_16_26 π ρ h6 ann f
  · exact image_16_27 π ρ h6 ann f
  · exact image_16_28 π ρ h6 ann f
  · exact image_16_29 π ρ h6 ann f
  · exact image_16_30 π ρ h6 ann f
  · exact image_16_31 π ρ h6 ann f
  · exact image_16_32 π ρ h6 ann f
  · exact image_16_33 π ρ h6 ann f
  · exact image_16_34 π ρ h6 ann f
  · exact image_16_35 π ρ h6 ann f
  · exact image_16_36 π ρ h6 ann f
  · exact image_16_37 π ρ h6 ann f
  · exact image_16_38 π ρ h6 ann f
  · exact image_16_39 π ρ h6 ann f
  · exact image_16_40 π ρ h6 ann f
  · exact image_16_41 π ρ h6 ann f
  · exact image_16_42 π ρ h6 ann f
  · exact image_16_43 π ρ h6 ann f
  · exact image_16_44 π ρ h6 ann f
  · exact image_16_45 π ρ h6 ann f
  · exact image_16_46 π ρ h6 ann f
end UniserialComputations.N6
