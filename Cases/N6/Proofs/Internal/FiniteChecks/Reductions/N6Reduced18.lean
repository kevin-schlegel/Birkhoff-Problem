import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_1080 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1080 v H)
lemma mul_reduced_1080 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]*x) + (word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1080 v H)
lemma reduced_1081 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1081 v H)
lemma mul_reduced_1081 (x : A) : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1081 v H)
lemma reduced_1082 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1082 v H)
lemma mul_reduced_1082 (x : A) : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1082 v H)
lemma reduced_1083 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1083 v H)
lemma mul_reduced_1083 (x : A) : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1083 v H)
lemma reduced_1084 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1084 v H)
lemma mul_reduced_1084 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]*x=(-(word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1084 v H)
lemma reduced_1085 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1085 v H)
lemma mul_reduced_1085 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1085 v H)
lemma reduced_1086 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1086 v H)
lemma mul_reduced_1086 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1086 v H)
lemma reduced_1087 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1087 v H)
lemma mul_reduced_1087 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]*x=(word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1087 v H)
lemma reduced_1088 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1088 v H)
lemma mul_reduced_1088 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1088 v H)
lemma reduced_1089 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1089 v H)
lemma mul_reduced_1089 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1089 v H)
lemma reduced_1090 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1090 v H)
lemma mul_reduced_1090 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1090 v H)
lemma reduced_1091 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1091 v H)
lemma mul_reduced_1091 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1091 v H)
lemma reduced_1092 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1092 v H)
lemma mul_reduced_1092 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1092 v H)
lemma reduced_1093 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1093 v H)
lemma mul_reduced_1093 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1093 v H)
lemma reduced_1094 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1094 v H)
lemma mul_reduced_1094 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1094 v H)
lemma reduced_1095 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1095 v H)
lemma mul_reduced_1095 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1095 v H)
lemma reduced_1096 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1096 v H)
lemma mul_reduced_1096 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1096 v H)
lemma reduced_1097 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1097 v H)
lemma mul_reduced_1097 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1097 v H)
lemma reduced_1098 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1098 v H)
lemma mul_reduced_1098 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1098 v H)
lemma reduced_1099 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1099 v H)
lemma mul_reduced_1099 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1099 v H)
lemma reduced_1100 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1100 v H)
lemma mul_reduced_1100 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1100 v H)
lemma reduced_1101 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1101 v H)
lemma mul_reduced_1101 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1101 v H)
lemma reduced_1102 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1102 v H)
lemma mul_reduced_1102 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1102 v H)
lemma reduced_1103 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1103 v H)
lemma mul_reduced_1103 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1103 v H)
lemma reduced_1104 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1104 v H)
lemma mul_reduced_1104 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1104 v H)
lemma reduced_1105 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1105 v H)
lemma mul_reduced_1105 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1105 v H)
lemma reduced_1106 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1106 v H)
lemma mul_reduced_1106 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1106 v H)
lemma reduced_1107 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1107 v H)
lemma mul_reduced_1107 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1107 v H)
lemma reduced_1108 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1108 v H)
lemma mul_reduced_1108 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1108 v H)
lemma reduced_1109 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1109 v H)
lemma mul_reduced_1109 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1109 v H)
lemma reduced_1110 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1110 v H)
lemma mul_reduced_1110 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]*x=(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1110 v H)
lemma reduced_1111 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1111 v H)
lemma mul_reduced_1111 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]*x=(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1111 v H)
lemma reduced_1112 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1112 v H)
lemma mul_reduced_1112 (x : A) : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1112 v H)
lemma reduced_1113 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1113 v H)
lemma mul_reduced_1113 (x : A) : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1113 v H)
lemma reduced_1114 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1114 v H)
lemma mul_reduced_1114 (x : A) : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1114 v H)
lemma reduced_1115 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1115 v H)
lemma mul_reduced_1115 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1115 v H)
lemma reduced_1116 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1116 v H)
lemma mul_reduced_1116 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]*x=(-(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1116 v H)
lemma reduced_1117 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1117 v H)
lemma mul_reduced_1117 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1117 v H)
lemma reduced_1118 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1118 v H)
lemma mul_reduced_1118 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]*x=(word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1118 v H)
lemma reduced_1119 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1119 v H)
lemma mul_reduced_1119 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]*x=(word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1119 v H)
lemma reduced_1120 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1120 v H)
lemma mul_reduced_1120 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]*x=(word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1120 v H)
lemma reduced_1121 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1121 v H)
lemma mul_reduced_1121 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]*x=(-(word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1121 v H)
lemma reduced_1122 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1122 v H)
lemma mul_reduced_1122 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]*x=(word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1122 v H)
lemma reduced_1123 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1123 v H)
lemma mul_reduced_1123 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1123 v H)
lemma reduced_1124 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]=word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1124 v H)
lemma mul_reduced_1124 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]*x=(word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1124 v H)
lemma reduced_1125 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1125 v H)
lemma mul_reduced_1125 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]*x=(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1125 v H)
lemma reduced_1126 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1126 v H)
lemma mul_reduced_1126 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]*x=(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1126 v H)
lemma reduced_1127 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1127 v H)
lemma mul_reduced_1127 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1127 v H)
lemma reduced_1128 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1128 v H)
lemma mul_reduced_1128 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1128 v H)
lemma reduced_1129 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1129 v H)
lemma mul_reduced_1129 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1129 v H)
lemma reduced_1130 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1130 v H)
lemma mul_reduced_1130 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1130 v H)
lemma reduced_1131 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1131 v H)
lemma mul_reduced_1131 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1131 v H)
lemma reduced_1132 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1132 v H)
lemma mul_reduced_1132 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]*x=(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1132 v H)
lemma reduced_1133 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1133 v H)
lemma mul_reduced_1133 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]*x=(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1133 v H)
lemma reduced_1134 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1134 v H)
lemma mul_reduced_1134 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1134 v H)
lemma reduced_1135 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1135 v H)
lemma mul_reduced_1135 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]*x) + (word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1135 v H)
lemma reduced_1136 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1136 v H)
lemma mul_reduced_1136 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1136 v H)
lemma reduced_1137 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1137 v H)
lemma mul_reduced_1137 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1137 v H)
lemma reduced_1138 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1138 v H)
lemma mul_reduced_1138 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]*x=(-(word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1138 v H)
lemma reduced_1139 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1139 v H)
lemma mul_reduced_1139 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]*x=(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1139 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_1080 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  exact Universal.reduced_1080 (a k) (relation_zero k)
lemma reduced_1081 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1081 (a k) (relation_zero k)
lemma reduced_1082 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1082 (a k) (relation_zero k)
lemma reduced_1083 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1083 (a k) (relation_zero k)
lemma reduced_1084 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_1084 (a k) (relation_zero k)
lemma reduced_1085 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_1085 (a k) (relation_zero k)
lemma reduced_1086 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_1086 (a k) (relation_zero k)
lemma reduced_1087 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_1087 (a k) (relation_zero k)
lemma reduced_1088 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_1088 (a k) (relation_zero k)
lemma reduced_1089 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_1089 (a k) (relation_zero k)
lemma reduced_1090 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_1090 (a k) (relation_zero k)
lemma reduced_1091 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_1091 (a k) (relation_zero k)
lemma reduced_1092 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_1092 (a k) (relation_zero k)
lemma reduced_1093 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_1093 (a k) (relation_zero k)
lemma reduced_1094 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_1094 (a k) (relation_zero k)
lemma reduced_1095 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_1095 (a k) (relation_zero k)
lemma reduced_1096 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_1096 (a k) (relation_zero k)
lemma reduced_1097 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_1097 (a k) (relation_zero k)
lemma reduced_1098 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_1098 (a k) (relation_zero k)
lemma reduced_1099 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_1099 (a k) (relation_zero k)
lemma reduced_1100 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_1100 (a k) (relation_zero k)
lemma reduced_1101 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_1101 (a k) (relation_zero k)
lemma reduced_1102 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_1102 (a k) (relation_zero k)
lemma reduced_1103 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_1103 (a k) (relation_zero k)
lemma reduced_1104 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_1104 (a k) (relation_zero k)
lemma reduced_1105 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_1105 (a k) (relation_zero k)
lemma reduced_1106 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_1106 (a k) (relation_zero k)
lemma reduced_1107 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_1107 (a k) (relation_zero k)
lemma reduced_1108 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_1108 (a k) (relation_zero k)
lemma reduced_1109 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_1109 (a k) (relation_zero k)
lemma reduced_1110 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_1110 (a k) (relation_zero k)
lemma reduced_1111 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_1111 (a k) (relation_zero k)
lemma reduced_1112 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1112 (a k) (relation_zero k)
lemma reduced_1113 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1113 (a k) (relation_zero k)
lemma reduced_1114 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1114 (a k) (relation_zero k)
lemma reduced_1115 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_1115 (a k) (relation_zero k)
lemma reduced_1116 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_1116 (a k) (relation_zero k)
lemma reduced_1117 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_1117 (a k) (relation_zero k)
lemma reduced_1118 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_1118 (a k) (relation_zero k)
lemma reduced_1119 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_1119 (a k) (relation_zero k)
lemma reduced_1120 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  exact Universal.reduced_1120 (a k) (relation_zero k)
lemma reduced_1121 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_1121 (a k) (relation_zero k)
lemma reduced_1122 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_1122 (a k) (relation_zero k)
lemma reduced_1123 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_1123 (a k) (relation_zero k)
lemma reduced_1124 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]=word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  exact Universal.reduced_1124 (a k) (relation_zero k)
lemma reduced_1125 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_1125 (a k) (relation_zero k)
lemma reduced_1126 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_1126 (a k) (relation_zero k)
lemma reduced_1127 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_1127 (a k) (relation_zero k)
lemma reduced_1128 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_1128 (a k) (relation_zero k)
lemma reduced_1129 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1129 (a k) (relation_zero k)
lemma reduced_1130 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1130 (a k) (relation_zero k)
lemma reduced_1131 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1131 (a k) (relation_zero k)
lemma reduced_1132 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_1132 (a k) (relation_zero k)
lemma reduced_1133 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_1133 (a k) (relation_zero k)
lemma reduced_1134 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1134 (a k) (relation_zero k)
lemma reduced_1135 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  exact Universal.reduced_1135 (a k) (relation_zero k)
lemma reduced_1136 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1136 (a k) (relation_zero k)
lemma reduced_1137 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1137 (a k) (relation_zero k)
lemma reduced_1138 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_1138 (a k) (relation_zero k)
lemma reduced_1139 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_1139 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
