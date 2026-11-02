import N6Constraints46
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
theorem image_46_0 (f : HomData π 46 0) : Normal k (homKind 46 0) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_1 (f : HomData π 46 1) : Normal k (homKind 46 1) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_2 (f : HomData π 46 2) : Normal k (homKind 46 2) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_3 (f : HomData π 46 3) : Normal k (homKind 46 3) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_4 (f : HomData π 46 4) : Normal k (homKind 46 4) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_5 (f : HomData π 46 5) : Normal k (homKind 46 5) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_6 (f : HomData π 46 6) : Normal k (homKind 46 6) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_7 (f : HomData π 46 7) : Normal k (homKind 46 7) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_8 (f : HomData π 46 8) : Normal k (homKind 46 8) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_9 (f : HomData π 46 9) : Normal k (homKind 46 9) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_10 (f : HomData π 46 10) : Normal k (homKind 46 10) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_11 (f : HomData π 46 11) : Normal k (homKind 46 11) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_12 (f : HomData π 46 12) : Normal k (homKind 46 12) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_13 (f : HomData π 46 13) : Normal k (homKind 46 13) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_14 (f : HomData π 46 14) : Normal k (homKind 46 14) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_15 (f : HomData π 46 15) : Normal k (homKind 46 15) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_16 (f : HomData π 46 16) : Normal k (homKind 46 16) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_17 (f : HomData π 46 17) : Normal k (homKind 46 17) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_18 (f : HomData π 46 18) : Normal k (homKind 46 18) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_19 (f : HomData π 46 19) : Normal k (homKind 46 19) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_20 (f : HomData π 46 20) : Normal k (homKind 46 20) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_21 (f : HomData π 46 21) : Normal k (homKind 46 21) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_22 (f : HomData π 46 22) : Normal k (homKind 46 22) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_23 (f : HomData π 46 23) : Normal k (homKind 46 23) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_24 (f : HomData π 46 24) : Normal k (homKind 46 24) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_25 (f : HomData π 46 25) : Normal k (homKind 46 25) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_26 (f : HomData π 46 26) : Normal k (homKind 46 26) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_27 (f : HomData π 46 27) : Normal k (homKind 46 27) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_28 (f : HomData π 46 28) : Normal k (homKind 46 28) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_29 (f : HomData π 46 29) : Normal k (homKind 46 29) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_30 (f : HomData π 46 30) : Normal k (homKind 46 30) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_31 (f : HomData π 46 31) : Normal k (homKind 46 31) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_32 (f : HomData π 46 32) : Normal k (homKind 46 32) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_33 (f : HomData π 46 33) : Normal k (homKind 46 33) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_34 (f : HomData π 46 34) : Normal k (homKind 46 34) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_35 (f : HomData π 46 35) : Normal k (homKind 46 35) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_36 (f : HomData π 46 36) : Normal k (homKind 46 36) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_37 (f : HomData π 46 37) : Normal k (homKind 46 37) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_38 (f : HomData π 46 38) : Normal k (homKind 46 38) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_39 (f : HomData π 46 39) : Normal k (homKind 46 39) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_40 (f : HomData π 46 40) : Normal k (homKind 46 40) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_41 (f : HomData π 46 41) : Normal k (homKind 46 41) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_42 (f : HomData π 46 42) : Normal k (homKind 46 42) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_43 (f : HomData π 46 43) : Normal k (homKind 46 43) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_44 (f : HomData π 46 44) : Normal k (homKind 46 44) (reduceHom π ρ f) := by
  change Normal k 5 (reduceHom π ρ f)
  apply normal_form_5
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_45 (f : HomData π 46 45) : Normal k (homKind 46 45) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_46_46 (f : HomData π 46 46) : Normal k (homKind 46 46) (reduceHom π ρ f) := by
  change Normal k 0 (reduceHom π ρ f)
  apply normal_form_0
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
  · norm_num [reduceHom,reduceMatrix,freeRank,freeSlot]
include h6 ann in
theorem image_row46 (j : Fin 47) (f : HomData π 46 j) : Normal k (homKind 46 j) (reduceHom π ρ f) := by
  fin_cases j
  · exact image_46_0 π ρ h6 ann f
  · exact image_46_1 π ρ h6 ann f
  · exact image_46_2 π ρ h6 ann f
  · exact image_46_3 π ρ h6 ann f
  · exact image_46_4 π ρ h6 ann f
  · exact image_46_5 π ρ h6 ann f
  · exact image_46_6 π ρ h6 ann f
  · exact image_46_7 π ρ h6 ann f
  · exact image_46_8 π ρ h6 ann f
  · exact image_46_9 π ρ h6 ann f
  · exact image_46_10 π ρ h6 ann f
  · exact image_46_11 π ρ h6 ann f
  · exact image_46_12 π ρ h6 ann f
  · exact image_46_13 π ρ h6 ann f
  · exact image_46_14 π ρ h6 ann f
  · exact image_46_15 π ρ h6 ann f
  · exact image_46_16 π ρ h6 ann f
  · exact image_46_17 π ρ h6 ann f
  · exact image_46_18 π ρ h6 ann f
  · exact image_46_19 π ρ h6 ann f
  · exact image_46_20 π ρ h6 ann f
  · exact image_46_21 π ρ h6 ann f
  · exact image_46_22 π ρ h6 ann f
  · exact image_46_23 π ρ h6 ann f
  · exact image_46_24 π ρ h6 ann f
  · exact image_46_25 π ρ h6 ann f
  · exact image_46_26 π ρ h6 ann f
  · exact image_46_27 π ρ h6 ann f
  · exact image_46_28 π ρ h6 ann f
  · exact image_46_29 π ρ h6 ann f
  · exact image_46_30 π ρ h6 ann f
  · exact image_46_31 π ρ h6 ann f
  · exact image_46_32 π ρ h6 ann f
  · exact image_46_33 π ρ h6 ann f
  · exact image_46_34 π ρ h6 ann f
  · exact image_46_35 π ρ h6 ann f
  · exact image_46_36 π ρ h6 ann f
  · exact image_46_37 π ρ h6 ann f
  · exact image_46_38 π ρ h6 ann f
  · exact image_46_39 π ρ h6 ann f
  · exact image_46_40 π ρ h6 ann f
  · exact image_46_41 π ρ h6 ann f
  · exact image_46_42 π ρ h6 ann f
  · exact image_46_43 π ρ h6 ann f
  · exact image_46_44 π ρ h6 ann f
  · exact image_46_45 π ρ h6 ann f
  · exact image_46_46 π ρ h6 ann f
end UniserialComputations.N6
