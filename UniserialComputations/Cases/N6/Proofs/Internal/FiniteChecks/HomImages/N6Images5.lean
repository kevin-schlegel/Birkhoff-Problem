import N6Constraints5
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
theorem image_5_0 (f : HomData π 5 0) : Normal k (homKind 5 0) (reduceHom π ρ f) := by
  have h00 := constraint_5_0_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_1 (f : HomData π 5 1) : Normal k (homKind 5 1) (reduceHom π ρ f) := by
  have h00 := constraint_5_1_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_2 (f : HomData π 5 2) : Normal k (homKind 5 2) (reduceHom π ρ f) := by
  have h00 := constraint_5_2_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_3 (f : HomData π 5 3) : Normal k (homKind 5 3) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_4 (f : HomData π 5 4) : Normal k (homKind 5 4) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_5 (f : HomData π 5 5) : Normal k (homKind 5 5) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_6 (f : HomData π 5 6) : Normal k (homKind 5 6) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_7 (f : HomData π 5 7) : Normal k (homKind 5 7) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_8 (f : HomData π 5 8) : Normal k (homKind 5 8) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_9 (f : HomData π 5 9) : Normal k (homKind 5 9) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_10 (f : HomData π 5 10) : Normal k (homKind 5 10) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_11 (f : HomData π 5 11) : Normal k (homKind 5 11) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_12 (f : HomData π 5 12) : Normal k (homKind 5 12) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_13 (f : HomData π 5 13) : Normal k (homKind 5 13) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_14 (f : HomData π 5 14) : Normal k (homKind 5 14) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_15 (f : HomData π 5 15) : Normal k (homKind 5 15) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_16 (f : HomData π 5 16) : Normal k (homKind 5 16) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_17 (f : HomData π 5 17) : Normal k (homKind 5 17) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_18 (f : HomData π 5 18) : Normal k (homKind 5 18) (reduceHom π ρ f) := by
  have h01 := constraint_5_18_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_19 (f : HomData π 5 19) : Normal k (homKind 5 19) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_20 (f : HomData π 5 20) : Normal k (homKind 5 20) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_21 (f : HomData π 5 21) : Normal k (homKind 5 21) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_22 (f : HomData π 5 22) : Normal k (homKind 5 22) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_23 (f : HomData π 5 23) : Normal k (homKind 5 23) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_24 (f : HomData π 5 24) : Normal k (homKind 5 24) (reduceHom π ρ f) := by
  have h01 := constraint_5_24_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_25 (f : HomData π 5 25) : Normal k (homKind 5 25) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_26 (f : HomData π 5 26) : Normal k (homKind 5 26) (reduceHom π ρ f) := by
  have h01 := constraint_5_26_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_27 (f : HomData π 5 27) : Normal k (homKind 5 27) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_28 (f : HomData π 5 28) : Normal k (homKind 5 28) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_29 (f : HomData π 5 29) : Normal k (homKind 5 29) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_30 (f : HomData π 5 30) : Normal k (homKind 5 30) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_31 (f : HomData π 5 31) : Normal k (homKind 5 31) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_32 (f : HomData π 5 32) : Normal k (homKind 5 32) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_33 (f : HomData π 5 33) : Normal k (homKind 5 33) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_34 (f : HomData π 5 34) : Normal k (homKind 5 34) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_35 (f : HomData π 5 35) : Normal k (homKind 5 35) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_36 (f : HomData π 5 36) : Normal k (homKind 5 36) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_37 (f : HomData π 5 37) : Normal k (homKind 5 37) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_38 (f : HomData π 5 38) : Normal k (homKind 5 38) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_39 (f : HomData π 5 39) : Normal k (homKind 5 39) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_40 (f : HomData π 5 40) : Normal k (homKind 5 40) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_41 (f : HomData π 5 41) : Normal k (homKind 5 41) (reduceHom π ρ f) := by
  have h01 := constraint_5_41_0_1 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h01
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h01
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_42 (f : HomData π 5 42) : Normal k (homKind 5 42) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_43 (f : HomData π 5 43) : Normal k (homKind 5 43) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_44 (f : HomData π 5 44) : Normal k (homKind 5 44) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_45 (f : HomData π 5 45) : Normal k (homKind 5 45) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_5_46 (f : HomData π 5 46) : Normal k (homKind 5 46) (reduceHom π ρ f) := by
  have h00 := constraint_5_46_0_0 π ρ h6 ann f
  try simp only [map_add,map_mul,map_neg,map_one] at h00
  change Normal k 1 (reduceHom π ρ f)
  apply normal_form_1
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
    linear_combination h00
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_row5 (j : Fin 47) (f : HomData π 5 j) : Normal k (homKind 5 j) (reduceHom π ρ f) := by
  fin_cases j
  · exact image_5_0 π ρ h6 ann f
  · exact image_5_1 π ρ h6 ann f
  · exact image_5_2 π ρ h6 ann f
  · exact image_5_3 π ρ h6 ann f
  · exact image_5_4 π ρ h6 ann f
  · exact image_5_5 π ρ h6 ann f
  · exact image_5_6 π ρ h6 ann f
  · exact image_5_7 π ρ h6 ann f
  · exact image_5_8 π ρ h6 ann f
  · exact image_5_9 π ρ h6 ann f
  · exact image_5_10 π ρ h6 ann f
  · exact image_5_11 π ρ h6 ann f
  · exact image_5_12 π ρ h6 ann f
  · exact image_5_13 π ρ h6 ann f
  · exact image_5_14 π ρ h6 ann f
  · exact image_5_15 π ρ h6 ann f
  · exact image_5_16 π ρ h6 ann f
  · exact image_5_17 π ρ h6 ann f
  · exact image_5_18 π ρ h6 ann f
  · exact image_5_19 π ρ h6 ann f
  · exact image_5_20 π ρ h6 ann f
  · exact image_5_21 π ρ h6 ann f
  · exact image_5_22 π ρ h6 ann f
  · exact image_5_23 π ρ h6 ann f
  · exact image_5_24 π ρ h6 ann f
  · exact image_5_25 π ρ h6 ann f
  · exact image_5_26 π ρ h6 ann f
  · exact image_5_27 π ρ h6 ann f
  · exact image_5_28 π ρ h6 ann f
  · exact image_5_29 π ρ h6 ann f
  · exact image_5_30 π ρ h6 ann f
  · exact image_5_31 π ρ h6 ann f
  · exact image_5_32 π ρ h6 ann f
  · exact image_5_33 π ρ h6 ann f
  · exact image_5_34 π ρ h6 ann f
  · exact image_5_35 π ρ h6 ann f
  · exact image_5_36 π ρ h6 ann f
  · exact image_5_37 π ρ h6 ann f
  · exact image_5_38 π ρ h6 ann f
  · exact image_5_39 π ρ h6 ann f
  · exact image_5_40 π ρ h6 ann f
  · exact image_5_41 π ρ h6 ann f
  · exact image_5_42 π ρ h6 ann f
  · exact image_5_43 π ρ h6 ann f
  · exact image_5_44 π ρ h6 ann f
  · exact image_5_45 π ρ h6 ann f
  · exact image_5_46 π ρ h6 ann f
end UniserialComputations.N6
