import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_0 : word v [1, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_0 v H)
lemma mul_reduced_0 (x : A) : word v [1, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_0 v H)
lemma reduced_1 : word v [3, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1 v H)
lemma mul_reduced_1 (x : A) : word v [3, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1 v H)
lemma reduced_2 : word v [4, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_2 v H)
lemma mul_reduced_2 (x : A) : word v [4, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_2 v H)
lemma reduced_3 : word v [5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_3 v H)
lemma mul_reduced_3 (x : A) : word v [5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_3 v H)
lemma reduced_4 : word v [5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_4 v H)
lemma mul_reduced_4 (x : A) : word v [5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_4 v H)
lemma reduced_5 : word v [8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_5 v H)
lemma mul_reduced_5 (x : A) : word v [8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_5 v H)
lemma reduced_6 : word v [9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_6 v H)
lemma mul_reduced_6 (x : A) : word v [9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_6 v H)
lemma reduced_7 : word v [16, 58]=word v [15, 1] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_7 v H)
lemma mul_reduced_7 (x : A) : word v [16, 58]*x=(word v [15, 1]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_7 v H)
lemma reduced_8 : word v [16, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_8 v H)
lemma mul_reduced_8 (x : A) : word v [16, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_8 v H)
lemma reduced_9 : word v [17, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_9 v H)
lemma mul_reduced_9 (x : A) : word v [17, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_9 v H)
lemma reduced_10 : word v [19, 52]=word v [18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_10 v H)
lemma mul_reduced_10 (x : A) : word v [19, 52]*x=(word v [18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_10 v H)
lemma reduced_11 : word v [20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_11 v H)
lemma mul_reduced_11 (x : A) : word v [20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_11 v H)
lemma reduced_12 : word v [21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_12 v H)
lemma mul_reduced_12 (x : A) : word v [21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_12 v H)
lemma reduced_13 : word v [23, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_13 v H)
lemma mul_reduced_13 (x : A) : word v [23, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_13 v H)
lemma reduced_14 : word v [23, 68]=(-word v [22, 3]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_14 v H)
lemma mul_reduced_14 (x : A) : word v [23, 68]*x=(-(word v [22, 3]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_14 v H)
lemma reduced_15 : word v [25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_15 v H)
lemma mul_reduced_15 (x : A) : word v [25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_15 v H)
lemma reduced_16 : word v [25, 62]=word v [24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_16 v H)
lemma mul_reduced_16 (x : A) : word v [25, 62]*x=(word v [24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_16 v H)
lemma reduced_17 : word v [26, 30]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_17 v H)
lemma mul_reduced_17 (x : A) : word v [26, 30]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_17 v H)
lemma reduced_18 : word v [27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_18 v H)
lemma mul_reduced_18 (x : A) : word v [27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_18 v H)
lemma reduced_19 : word v [29, 18]=word v [28, 14] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_19 v H)
lemma mul_reduced_19 (x : A) : word v [29, 18]*x=(word v [28, 14]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_19 v H)
lemma reduced_20 : word v [31, 72]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_20 v H)
lemma mul_reduced_20 (x : A) : word v [31, 72]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_20 v H)
lemma reduced_21 : word v [32, 60]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_21 v H)
lemma mul_reduced_21 (x : A) : word v [32, 60]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_21 v H)
lemma reduced_22 : word v [34, 65]=word v [33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_22 v H)
lemma mul_reduced_22 (x : A) : word v [34, 65]*x=(word v [33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_22 v H)
lemma reduced_23 : word v [35, 54]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_23 v H)
lemma mul_reduced_23 (x : A) : word v [35, 54]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_23 v H)
lemma reduced_24 : word v [36, 69]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_24 v H)
lemma mul_reduced_24 (x : A) : word v [36, 69]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_24 v H)
lemma reduced_25 : word v [38, 29]=word v [37, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_25 v H)
lemma mul_reduced_25 (x : A) : word v [38, 29]*x=(word v [37, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_25 v H)
lemma reduced_26 : word v [40, 61]=word v [39, 12] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_26 v H)
lemma mul_reduced_26 (x : A) : word v [40, 61]*x=(word v [39, 12]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_26 v H)
lemma reduced_27 : word v [42, 46]=word v [41, 43] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_27 v H)
lemma mul_reduced_27 (x : A) : word v [42, 46]*x=(word v [41, 43]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_27 v H)
lemma reduced_28 : word v [44, 59]=word v [43, 48] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_28 v H)
lemma mul_reduced_28 (x : A) : word v [44, 59]*x=(word v [43, 48]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_28 v H)
lemma reduced_29 : word v [46, 47]=word v [45, 6] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_29 v H)
lemma mul_reduced_29 (x : A) : word v [46, 47]*x=(word v [45, 6]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_29 v H)
lemma reduced_30 : word v [48, 50]=word v [47, 7] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_30 v H)
lemma mul_reduced_30 (x : A) : word v [48, 50]*x=(word v [47, 7]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_30 v H)
lemma reduced_31 : word v [49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_31 v H)
lemma mul_reduced_31 (x : A) : word v [49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_31 v H)
lemma reduced_32 : word v [51, 63]=word v [50, 17] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_32 v H)
lemma mul_reduced_32 (x : A) : word v [51, 63]*x=(word v [50, 17]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_32 v H)
lemma reduced_33 : word v [53, 56]=word v [52, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_33 v H)
lemma mul_reduced_33 (x : A) : word v [53, 56]*x=(word v [52, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_33 v H)
lemma reduced_34 : word v [56, 44]=word v [54, 16] + word v [55, 27] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_34 v H)
lemma mul_reduced_34 (x : A) : word v [56, 44]*x=(word v [54, 16]*x) + (word v [55, 27]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_34 v H)
lemma reduced_35 : word v [59, 51]=(-word v [57, 5]) + word v [58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_35 v H)
lemma mul_reduced_35 (x : A) : word v [59, 51]*x=(-(word v [57, 5]*x)) + (word v [58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_35 v H)
lemma reduced_36 : word v [62, 53]=word v [60, 4] + word v [61, 35] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_36 v H)
lemma mul_reduced_36 (x : A) : word v [62, 53]*x=(word v [60, 4]*x) + (word v [61, 35]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_36 v H)
lemma reduced_37 : word v [65, 49]=(-word v [63, 21]) + word v [64, 36] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_37 v H)
lemma mul_reduced_37 (x : A) : word v [65, 49]*x=(-(word v [63, 21]*x)) + (word v [64, 36]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_37 v H)
lemma reduced_38 : word v [68, 40]=(-word v [66, 25]) + word v [67, 32] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_38 v H)
lemma mul_reduced_38 (x : A) : word v [68, 40]*x=(-(word v [66, 25]*x)) + (word v [67, 32]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_38 v H)
lemma reduced_39 : word v [71, 73]=word v [69, 8] + word v [70, 23] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_39 v H)
lemma mul_reduced_39 (x : A) : word v [71, 73]*x=(word v [69, 8]*x) + (word v [70, 23]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_39 v H)
lemma reduced_40 : word v [73, 66]=word v [72, 37] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_40 v H)
lemma mul_reduced_40 (x : A) : word v [73, 66]*x=(word v [72, 37]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_40 v H)
lemma reduced_41 : word v [15, 1, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_41 v H)
lemma mul_reduced_41 (x : A) : word v [15, 1, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_41 v H)
lemma reduced_42 : word v [1, 34, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_42 v H)
lemma mul_reduced_42 (x : A) : word v [1, 34, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_42 v H)
lemma reduced_43 : word v [22, 3, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_43 v H)
lemma mul_reduced_43 (x : A) : word v [22, 3, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_43 v H)
lemma reduced_44 : word v [60, 4, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_44 v H)
lemma mul_reduced_44 (x : A) : word v [60, 4, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_44 v H)
lemma reduced_45 : word v [4, 56, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_45 v H)
lemma mul_reduced_45 (x : A) : word v [4, 56, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_45 v H)
lemma reduced_46 : word v [57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_46 v H)
lemma mul_reduced_46 (x : A) : word v [57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_46 v H)
lemma reduced_47 : word v [57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_47 v H)
lemma mul_reduced_47 (x : A) : word v [57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_47 v H)
lemma reduced_48 : word v [8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_48 v H)
lemma mul_reduced_48 (x : A) : word v [8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_48 v H)
lemma reduced_49 : word v [69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_49 v H)
lemma mul_reduced_49 (x : A) : word v [69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_49 v H)
lemma reduced_50 : word v [14, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_50 v H)
lemma mul_reduced_50 (x : A) : word v [14, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_50 v H)
lemma reduced_51 : word v [18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_51 v H)
lemma mul_reduced_51 (x : A) : word v [18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_51 v H)
lemma reduced_52 : word v [54, 16, 58]=word v [54, 15, 1] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_52 v H)
lemma mul_reduced_52 (x : A) : word v [54, 16, 58]*x=(word v [54, 15, 1]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_52 v H)
lemma reduced_53 : word v [54, 16, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_53 v H)
lemma mul_reduced_53 (x : A) : word v [54, 16, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_53 v H)
lemma reduced_54 : word v [7, 17, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_54 v H)
lemma mul_reduced_54 (x : A) : word v [7, 17, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_54 v H)
lemma reduced_55 : word v [50, 17, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_55 v H)
lemma mul_reduced_55 (x : A) : word v [50, 17, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_55 v H)
lemma reduced_56 : word v [19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_56 v H)
lemma mul_reduced_56 (x : A) : word v [19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_56 v H)
lemma reduced_57 : word v [24, 19, 52]=word v [24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_57 v H)
lemma mul_reduced_57 (x : A) : word v [24, 19, 52]*x=(word v [24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_57 v H)
lemma reduced_58 : word v [29, 19, 52]=word v [28, 14, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_58 v H)
lemma mul_reduced_58 (x : A) : word v [29, 19, 52]*x=(word v [28, 14, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_58 v H)
lemma reduced_59 : word v [63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_59 v H)
lemma mul_reduced_59 (x : A) : word v [63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_59 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_0 : word (a k) [1, 33]=0 := by
  exact Universal.reduced_0 (a k) (relation_zero k)
lemma reduced_1 : word (a k) [3, 39]=0 := by
  exact Universal.reduced_1 (a k) (relation_zero k)
lemma reduced_2 : word (a k) [4, 55]=0 := by
  exact Universal.reduced_2 (a k) (relation_zero k)
lemma reduced_3 : word (a k) [5, 64]=0 := by
  exact Universal.reduced_3 (a k) (relation_zero k)
lemma reduced_4 : word (a k) [5, 65]=0 := by
  exact Universal.reduced_4 (a k) (relation_zero k)
lemma reduced_5 : word (a k) [8, 67]=0 := by
  exact Universal.reduced_5 (a k) (relation_zero k)
lemma reduced_6 : word (a k) [9, 42]=0 := by
  exact Universal.reduced_6 (a k) (relation_zero k)
lemma reduced_7 : word (a k) [16, 58]=word (a k) [15, 1] := by
  exact Universal.reduced_7 (a k) (relation_zero k)
lemma reduced_8 : word (a k) [16, 59]=0 := by
  exact Universal.reduced_8 (a k) (relation_zero k)
lemma reduced_9 : word (a k) [17, 20]=0 := by
  exact Universal.reduced_9 (a k) (relation_zero k)
lemma reduced_10 : word (a k) [19, 52]=word (a k) [18, 9] := by
  exact Universal.reduced_10 (a k) (relation_zero k)
lemma reduced_11 : word (a k) [20, 31]=0 := by
  exact Universal.reduced_11 (a k) (relation_zero k)
lemma reduced_12 : word (a k) [21, 71]=0 := by
  exact Universal.reduced_12 (a k) (relation_zero k)
lemma reduced_13 : word (a k) [23, 67]=0 := by
  exact Universal.reduced_13 (a k) (relation_zero k)
lemma reduced_14 : word (a k) [23, 68]=(-word (a k) [22, 3]) := by
  exact Universal.reduced_14 (a k) (relation_zero k)
lemma reduced_15 : word (a k) [25, 61]=0 := by
  exact Universal.reduced_15 (a k) (relation_zero k)
lemma reduced_16 : word (a k) [25, 62]=word (a k) [24, 19] := by
  exact Universal.reduced_16 (a k) (relation_zero k)
lemma reduced_17 : word (a k) [26, 30]=0 := by
  exact Universal.reduced_17 (a k) (relation_zero k)
lemma reduced_18 : word (a k) [27, 57]=0 := by
  exact Universal.reduced_18 (a k) (relation_zero k)
lemma reduced_19 : word (a k) [29, 18]=word (a k) [28, 14] := by
  exact Universal.reduced_19 (a k) (relation_zero k)
lemma reduced_20 : word (a k) [31, 72]=0 := by
  exact Universal.reduced_20 (a k) (relation_zero k)
lemma reduced_21 : word (a k) [32, 60]=0 := by
  exact Universal.reduced_21 (a k) (relation_zero k)
lemma reduced_22 : word (a k) [34, 65]=word (a k) [33, 13] := by
  exact Universal.reduced_22 (a k) (relation_zero k)
lemma reduced_23 : word (a k) [35, 54]=0 := by
  exact Universal.reduced_23 (a k) (relation_zero k)
lemma reduced_24 : word (a k) [36, 69]=0 := by
  exact Universal.reduced_24 (a k) (relation_zero k)
lemma reduced_25 : word (a k) [38, 29]=word (a k) [37, 24] := by
  exact Universal.reduced_25 (a k) (relation_zero k)
lemma reduced_26 : word (a k) [40, 61]=word (a k) [39, 12] := by
  exact Universal.reduced_26 (a k) (relation_zero k)
lemma reduced_27 : word (a k) [42, 46]=word (a k) [41, 43] := by
  exact Universal.reduced_27 (a k) (relation_zero k)
lemma reduced_28 : word (a k) [44, 59]=word (a k) [43, 48] := by
  exact Universal.reduced_28 (a k) (relation_zero k)
lemma reduced_29 : word (a k) [46, 47]=word (a k) [45, 6] := by
  exact Universal.reduced_29 (a k) (relation_zero k)
lemma reduced_30 : word (a k) [48, 50]=word (a k) [47, 7] := by
  exact Universal.reduced_30 (a k) (relation_zero k)
lemma reduced_31 : word (a k) [49, 70]=0 := by
  exact Universal.reduced_31 (a k) (relation_zero k)
lemma reduced_32 : word (a k) [51, 63]=word (a k) [50, 17] := by
  exact Universal.reduced_32 (a k) (relation_zero k)
lemma reduced_33 : word (a k) [53, 56]=word (a k) [52, 41] := by
  exact Universal.reduced_33 (a k) (relation_zero k)
lemma reduced_34 : word (a k) [56, 44]=word (a k) [54, 16] + word (a k) [55, 27] := by
  exact Universal.reduced_34 (a k) (relation_zero k)
lemma reduced_35 : word (a k) [59, 51]=(-word (a k) [57, 5]) + word (a k) [58, 34] := by
  exact Universal.reduced_35 (a k) (relation_zero k)
lemma reduced_36 : word (a k) [62, 53]=word (a k) [60, 4] + word (a k) [61, 35] := by
  exact Universal.reduced_36 (a k) (relation_zero k)
lemma reduced_37 : word (a k) [65, 49]=(-word (a k) [63, 21]) + word (a k) [64, 36] := by
  exact Universal.reduced_37 (a k) (relation_zero k)
lemma reduced_38 : word (a k) [68, 40]=(-word (a k) [66, 25]) + word (a k) [67, 32] := by
  exact Universal.reduced_38 (a k) (relation_zero k)
lemma reduced_39 : word (a k) [71, 73]=word (a k) [69, 8] + word (a k) [70, 23] := by
  exact Universal.reduced_39 (a k) (relation_zero k)
lemma reduced_40 : word (a k) [73, 66]=word (a k) [72, 37] := by
  exact Universal.reduced_40 (a k) (relation_zero k)
lemma reduced_41 : word (a k) [15, 1, 33]=0 := by
  exact Universal.reduced_41 (a k) (relation_zero k)
lemma reduced_42 : word (a k) [1, 34, 64]=0 := by
  exact Universal.reduced_42 (a k) (relation_zero k)
lemma reduced_43 : word (a k) [22, 3, 39]=0 := by
  exact Universal.reduced_43 (a k) (relation_zero k)
lemma reduced_44 : word (a k) [60, 4, 55]=0 := by
  exact Universal.reduced_44 (a k) (relation_zero k)
lemma reduced_45 : word (a k) [4, 56, 43]=0 := by
  exact Universal.reduced_45 (a k) (relation_zero k)
lemma reduced_46 : word (a k) [57, 5, 64]=0 := by
  exact Universal.reduced_46 (a k) (relation_zero k)
lemma reduced_47 : word (a k) [57, 5, 65]=0 := by
  exact Universal.reduced_47 (a k) (relation_zero k)
lemma reduced_48 : word (a k) [8, 68, 39]=0 := by
  exact Universal.reduced_48 (a k) (relation_zero k)
lemma reduced_49 : word (a k) [69, 8, 67]=0 := by
  exact Universal.reduced_49 (a k) (relation_zero k)
lemma reduced_50 : word (a k) [14, 9, 42]=0 := by
  exact Universal.reduced_50 (a k) (relation_zero k)
lemma reduced_51 : word (a k) [18, 9, 42]=0 := by
  exact Universal.reduced_51 (a k) (relation_zero k)
lemma reduced_52 : word (a k) [54, 16, 58]=word (a k) [54, 15, 1] := by
  exact Universal.reduced_52 (a k) (relation_zero k)
lemma reduced_53 : word (a k) [54, 16, 59]=0 := by
  exact Universal.reduced_53 (a k) (relation_zero k)
lemma reduced_54 : word (a k) [7, 17, 20]=0 := by
  exact Universal.reduced_54 (a k) (relation_zero k)
lemma reduced_55 : word (a k) [50, 17, 20]=0 := by
  exact Universal.reduced_55 (a k) (relation_zero k)
lemma reduced_56 : word (a k) [19, 53, 55]=0 := by
  exact Universal.reduced_56 (a k) (relation_zero k)
lemma reduced_57 : word (a k) [24, 19, 52]=word (a k) [24, 18, 9] := by
  exact Universal.reduced_57 (a k) (relation_zero k)
lemma reduced_58 : word (a k) [29, 19, 52]=word (a k) [28, 14, 9] := by
  exact Universal.reduced_58 (a k) (relation_zero k)
lemma reduced_59 : word (a k) [63, 20, 31]=0 := by
  exact Universal.reduced_59 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
