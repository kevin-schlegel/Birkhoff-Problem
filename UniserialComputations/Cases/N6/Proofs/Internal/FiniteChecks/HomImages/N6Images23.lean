import N6Constraints23
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
theorem image_23_0 (f : HomData π 23 0) : Normal k (homKind 23 0) (reduceHom π ρ f) := by
  have h00 := constraint_23_0_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_1 (f : HomData π 23 1) : Normal k (homKind 23 1) (reduceHom π ρ f) := by
  have h00 := constraint_23_1_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_2 (f : HomData π 23 2) : Normal k (homKind 23 2) (reduceHom π ρ f) := by
  have h00 := constraint_23_2_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_3 (f : HomData π 23 3) : Normal k (homKind 23 3) (reduceHom π ρ f) := by
  have h00 := constraint_23_3_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_4 (f : HomData π 23 4) : Normal k (homKind 23 4) (reduceHom π ρ f) := by
  have h00 := constraint_23_4_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_5 (f : HomData π 23 5) : Normal k (homKind 23 5) (reduceHom π ρ f) := by
  have h00 := constraint_23_5_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_6 (f : HomData π 23 6) : Normal k (homKind 23 6) (reduceHom π ρ f) := by
  have h00 := constraint_23_6_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_7 (f : HomData π 23 7) : Normal k (homKind 23 7) (reduceHom π ρ f) := by
  have h00 := constraint_23_7_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_8 (f : HomData π 23 8) : Normal k (homKind 23 8) (reduceHom π ρ f) := by
  have h00 := constraint_23_8_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_9 (f : HomData π 23 9) : Normal k (homKind 23 9) (reduceHom π ρ f) := by
  have h00 := constraint_23_9_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_10 (f : HomData π 23 10) : Normal k (homKind 23 10) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_11 (f : HomData π 23 11) : Normal k (homKind 23 11) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_12 (f : HomData π 23 12) : Normal k (homKind 23 12) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_13 (f : HomData π 23 13) : Normal k (homKind 23 13) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_14 (f : HomData π 23 14) : Normal k (homKind 23 14) (reduceHom π ρ f) := by
  have h00 := constraint_23_14_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_15 (f : HomData π 23 15) : Normal k (homKind 23 15) (reduceHom π ρ f) := by
  have h00 := constraint_23_15_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_16 (f : HomData π 23 16) : Normal k (homKind 23 16) (reduceHom π ρ f) := by
  have h00 := constraint_23_16_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_17 (f : HomData π 23 17) : Normal k (homKind 23 17) (reduceHom π ρ f) := by
  have h00 := constraint_23_17_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_18 (f : HomData π 23 18) : Normal k (homKind 23 18) (reduceHom π ρ f) := by
  have h00 := constraint_23_18_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  have h01 := constraint_23_18_0_1 π ρ h6 ann f
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
theorem image_23_19 (f : HomData π 23 19) : Normal k (homKind 23 19) (reduceHom π ρ f) := by
  have h00 := constraint_23_19_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_20 (f : HomData π 23 20) : Normal k (homKind 23 20) (reduceHom π ρ f) := by
  have h00 := constraint_23_20_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_21 (f : HomData π 23 21) : Normal k (homKind 23 21) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_22 (f : HomData π 23 22) : Normal k (homKind 23 22) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_23 (f : HomData π 23 23) : Normal k (homKind 23 23) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_24 (f : HomData π 23 24) : Normal k (homKind 23 24) (reduceHom π ρ f) := by
  have h01 := constraint_23_24_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_25 (f : HomData π 23 25) : Normal k (homKind 23 25) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_26 (f : HomData π 23 26) : Normal k (homKind 23 26) (reduceHom π ρ f) := by
  have h01 := constraint_23_26_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_27 (f : HomData π 23 27) : Normal k (homKind 23 27) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_28 (f : HomData π 23 28) : Normal k (homKind 23 28) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_29 (f : HomData π 23 29) : Normal k (homKind 23 29) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_30 (f : HomData π 23 30) : Normal k (homKind 23 30) (reduceHom π ρ f) := by
  have h01 := constraint_23_30_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_31 (f : HomData π 23 31) : Normal k (homKind 23 31) (reduceHom π ρ f) := by
  have h01 := constraint_23_31_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_32 (f : HomData π 23 32) : Normal k (homKind 23 32) (reduceHom π ρ f) := by
  have h01 := constraint_23_32_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_33 (f : HomData π 23 33) : Normal k (homKind 23 33) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_34 (f : HomData π 23 34) : Normal k (homKind 23 34) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_35 (f : HomData π 23 35) : Normal k (homKind 23 35) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_36 (f : HomData π 23 36) : Normal k (homKind 23 36) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_37 (f : HomData π 23 37) : Normal k (homKind 23 37) (reduceHom π ρ f) := by
  have h01 := constraint_23_37_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_38 (f : HomData π 23 38) : Normal k (homKind 23 38) (reduceHom π ρ f) := by
  have h01 := constraint_23_38_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_39 (f : HomData π 23 39) : Normal k (homKind 23 39) (reduceHom π ρ f) := by
  have h01 := constraint_23_39_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_40 (f : HomData π 23 40) : Normal k (homKind 23 40) (reduceHom π ρ f) := by
  have h01 := constraint_23_40_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_41 (f : HomData π 23 41) : Normal k (homKind 23 41) (reduceHom π ρ f) := by
  have h01 := constraint_23_41_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_42 (f : HomData π 23 42) : Normal k (homKind 23 42) (reduceHom π ρ f) := by
  have h01 := constraint_23_42_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_43 (f : HomData π 23 43) : Normal k (homKind 23 43) (reduceHom π ρ f) := by
  have h01 := constraint_23_43_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 11 (reduceHom π ρ f)
  apply normal_form_11
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_44 (f : HomData π 23 44) : Normal k (homKind 23 44) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_45 (f : HomData π 23 45) : Normal k (homKind 23 45) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_23_46 (f : HomData π 23 46) : Normal k (homKind 23 46) (reduceHom π ρ f) := by
  have h00 := constraint_23_46_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_row23 (j : Fin 47) (f : HomData π 23 j) : Normal k (homKind 23 j) (reduceHom π ρ f) := by
  fin_cases j
  · exact image_23_0 π ρ h6 ann f
  · exact image_23_1 π ρ h6 ann f
  · exact image_23_2 π ρ h6 ann f
  · exact image_23_3 π ρ h6 ann f
  · exact image_23_4 π ρ h6 ann f
  · exact image_23_5 π ρ h6 ann f
  · exact image_23_6 π ρ h6 ann f
  · exact image_23_7 π ρ h6 ann f
  · exact image_23_8 π ρ h6 ann f
  · exact image_23_9 π ρ h6 ann f
  · exact image_23_10 π ρ h6 ann f
  · exact image_23_11 π ρ h6 ann f
  · exact image_23_12 π ρ h6 ann f
  · exact image_23_13 π ρ h6 ann f
  · exact image_23_14 π ρ h6 ann f
  · exact image_23_15 π ρ h6 ann f
  · exact image_23_16 π ρ h6 ann f
  · exact image_23_17 π ρ h6 ann f
  · exact image_23_18 π ρ h6 ann f
  · exact image_23_19 π ρ h6 ann f
  · exact image_23_20 π ρ h6 ann f
  · exact image_23_21 π ρ h6 ann f
  · exact image_23_22 π ρ h6 ann f
  · exact image_23_23 π ρ h6 ann f
  · exact image_23_24 π ρ h6 ann f
  · exact image_23_25 π ρ h6 ann f
  · exact image_23_26 π ρ h6 ann f
  · exact image_23_27 π ρ h6 ann f
  · exact image_23_28 π ρ h6 ann f
  · exact image_23_29 π ρ h6 ann f
  · exact image_23_30 π ρ h6 ann f
  · exact image_23_31 π ρ h6 ann f
  · exact image_23_32 π ρ h6 ann f
  · exact image_23_33 π ρ h6 ann f
  · exact image_23_34 π ρ h6 ann f
  · exact image_23_35 π ρ h6 ann f
  · exact image_23_36 π ρ h6 ann f
  · exact image_23_37 π ρ h6 ann f
  · exact image_23_38 π ρ h6 ann f
  · exact image_23_39 π ρ h6 ann f
  · exact image_23_40 π ρ h6 ann f
  · exact image_23_41 π ρ h6 ann f
  · exact image_23_42 π ρ h6 ann f
  · exact image_23_43 π ρ h6 ann f
  · exact image_23_44 π ρ h6 ann f
  · exact image_23_45 π ρ h6 ann f
  · exact image_23_46 π ρ h6 ann f
end UniserialComputations.N6
