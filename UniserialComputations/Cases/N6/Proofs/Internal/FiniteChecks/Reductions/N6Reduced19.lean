import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_1140 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1140 v H)
lemma mul_reduced_1140 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]*x=(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1140 v H)
lemma reduced_1141 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1141 v H)
lemma mul_reduced_1141 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1141 v H)
lemma reduced_1142 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1142 v H)
lemma mul_reduced_1142 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1142 v H)
lemma reduced_1143 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1143 v H)
lemma mul_reduced_1143 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1143 v H)
lemma reduced_1144 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1144 v H)
lemma mul_reduced_1144 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1144 v H)
lemma reduced_1145 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1145 v H)
lemma mul_reduced_1145 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1145 v H)
lemma reduced_1146 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1146 v H)
lemma mul_reduced_1146 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1146 v H)
lemma reduced_1147 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1147 v H)
lemma mul_reduced_1147 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1147 v H)
lemma reduced_1148 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1148 v H)
lemma mul_reduced_1148 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1148 v H)
lemma reduced_1149 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1149 v H)
lemma mul_reduced_1149 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1149 v H)
lemma reduced_1150 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1150 v H)
lemma mul_reduced_1150 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1150 v H)
lemma reduced_1151 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1151 v H)
lemma mul_reduced_1151 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1151 v H)
lemma reduced_1152 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1152 v H)
lemma mul_reduced_1152 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1152 v H)
lemma reduced_1153 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1153 v H)
lemma mul_reduced_1153 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1153 v H)
lemma reduced_1154 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1154 v H)
lemma mul_reduced_1154 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1154 v H)
lemma reduced_1155 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1155 v H)
lemma mul_reduced_1155 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1155 v H)
lemma reduced_1156 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1156 v H)
lemma mul_reduced_1156 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1156 v H)
lemma reduced_1157 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1157 v H)
lemma mul_reduced_1157 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1157 v H)
lemma reduced_1158 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1158 v H)
lemma mul_reduced_1158 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1158 v H)
lemma reduced_1159 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1159 v H)
lemma mul_reduced_1159 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1159 v H)
lemma reduced_1160 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1160 v H)
lemma mul_reduced_1160 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1160 v H)
lemma reduced_1161 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1161 v H)
lemma mul_reduced_1161 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1161 v H)
lemma reduced_1162 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1162 v H)
lemma mul_reduced_1162 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1162 v H)
lemma reduced_1163 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1163 v H)
lemma mul_reduced_1163 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]*x=(word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1163 v H)
lemma reduced_1164 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1164 v H)
lemma mul_reduced_1164 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1164 v H)
lemma reduced_1165 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1165 v H)
lemma mul_reduced_1165 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1165 v H)
lemma reduced_1166 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1166 v H)
lemma mul_reduced_1166 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1166 v H)
lemma reduced_1167 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1167 v H)
lemma mul_reduced_1167 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1167 v H)
lemma reduced_1168 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1168 v H)
lemma mul_reduced_1168 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]*x=(-(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1168 v H)
lemma reduced_1169 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1169 v H)
lemma mul_reduced_1169 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1169 v H)
lemma reduced_1170 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1170 v H)
lemma mul_reduced_1170 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]*x=(word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1170 v H)
lemma reduced_1171 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1171 v H)
lemma mul_reduced_1171 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]*x=(word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1171 v H)
lemma reduced_1172 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1172 v H)
lemma mul_reduced_1172 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]*x=(-(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1172 v H)
lemma reduced_1173 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1173 v H)
lemma mul_reduced_1173 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1173 v H)
lemma reduced_1174 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1174 v H)
lemma mul_reduced_1174 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1174 v H)
lemma reduced_1175 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1175 v H)
lemma mul_reduced_1175 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]*x=(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1175 v H)
lemma reduced_1176 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1176 v H)
lemma mul_reduced_1176 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]*x=(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1176 v H)
lemma reduced_1177 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1177 v H)
lemma mul_reduced_1177 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1177 v H)
lemma reduced_1178 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1178 v H)
lemma mul_reduced_1178 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1178 v H)
lemma reduced_1179 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1179 v H)
lemma mul_reduced_1179 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1179 v H)
lemma reduced_1180 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1180 v H)
lemma mul_reduced_1180 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1180 v H)
lemma reduced_1181 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1181 v H)
lemma mul_reduced_1181 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]*x=(word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1181 v H)
lemma reduced_1182 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1182 v H)
lemma mul_reduced_1182 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1182 v H)
lemma reduced_1183 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1183 v H)
lemma mul_reduced_1183 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1183 v H)
lemma reduced_1184 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1184 v H)
lemma mul_reduced_1184 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1184 v H)
lemma reduced_1185 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1185 v H)
lemma mul_reduced_1185 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]*x=(word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]*x) + (word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1185 v H)
lemma reduced_1186 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1186 v H)
lemma mul_reduced_1186 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]*x=(-(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1186 v H)
lemma reduced_1187 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1187 v H)
lemma mul_reduced_1187 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1187 v H)
lemma reduced_1188 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1188 v H)
lemma mul_reduced_1188 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1188 v H)
lemma reduced_1189 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1189 v H)
lemma mul_reduced_1189 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]*x=(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1189 v H)
lemma reduced_1190 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1190 v H)
lemma mul_reduced_1190 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1190 v H)
lemma reduced_1191 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1191 v H)
lemma mul_reduced_1191 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1191 v H)
lemma reduced_1192 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1192 v H)
lemma mul_reduced_1192 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1192 v H)
lemma reduced_1193 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1193 v H)
lemma mul_reduced_1193 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1193 v H)
lemma reduced_1194 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1194 v H)
lemma mul_reduced_1194 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1194 v H)
lemma reduced_1195 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1195 v H)
lemma mul_reduced_1195 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1195 v H)
lemma reduced_1196 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1196 v H)
lemma mul_reduced_1196 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1196 v H)
lemma reduced_1197 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1197 v H)
lemma mul_reduced_1197 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1197 v H)
lemma reduced_1198 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1198 v H)
lemma mul_reduced_1198 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1198 v H)
lemma reduced_1199 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1199 v H)
lemma mul_reduced_1199 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1199 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_1140 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_1140 (a k) (relation_zero k)
lemma reduced_1141 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_1141 (a k) (relation_zero k)
lemma reduced_1142 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_1142 (a k) (relation_zero k)
lemma reduced_1143 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_1143 (a k) (relation_zero k)
lemma reduced_1144 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_1144 (a k) (relation_zero k)
lemma reduced_1145 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_1145 (a k) (relation_zero k)
lemma reduced_1146 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_1146 (a k) (relation_zero k)
lemma reduced_1147 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_1147 (a k) (relation_zero k)
lemma reduced_1148 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_1148 (a k) (relation_zero k)
lemma reduced_1149 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_1149 (a k) (relation_zero k)
lemma reduced_1150 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_1150 (a k) (relation_zero k)
lemma reduced_1151 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_1151 (a k) (relation_zero k)
lemma reduced_1152 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_1152 (a k) (relation_zero k)
lemma reduced_1153 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_1153 (a k) (relation_zero k)
lemma reduced_1154 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_1154 (a k) (relation_zero k)
lemma reduced_1155 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_1155 (a k) (relation_zero k)
lemma reduced_1156 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_1156 (a k) (relation_zero k)
lemma reduced_1157 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_1157 (a k) (relation_zero k)
lemma reduced_1158 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_1158 (a k) (relation_zero k)
lemma reduced_1159 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_1159 (a k) (relation_zero k)
lemma reduced_1160 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_1160 (a k) (relation_zero k)
lemma reduced_1161 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_1161 (a k) (relation_zero k)
lemma reduced_1162 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_1162 (a k) (relation_zero k)
lemma reduced_1163 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_1163 (a k) (relation_zero k)
lemma reduced_1164 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1164 (a k) (relation_zero k)
lemma reduced_1165 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1165 (a k) (relation_zero k)
lemma reduced_1166 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1166 (a k) (relation_zero k)
lemma reduced_1167 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_1167 (a k) (relation_zero k)
lemma reduced_1168 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_1168 (a k) (relation_zero k)
lemma reduced_1169 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_1169 (a k) (relation_zero k)
lemma reduced_1170 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_1170 (a k) (relation_zero k)
lemma reduced_1171 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_1171 (a k) (relation_zero k)
lemma reduced_1172 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_1172 (a k) (relation_zero k)
lemma reduced_1173 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_1173 (a k) (relation_zero k)
lemma reduced_1174 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_1174 (a k) (relation_zero k)
lemma reduced_1175 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_1175 (a k) (relation_zero k)
lemma reduced_1176 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_1176 (a k) (relation_zero k)
lemma reduced_1177 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_1177 (a k) (relation_zero k)
lemma reduced_1178 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_1178 (a k) (relation_zero k)
lemma reduced_1179 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1179 (a k) (relation_zero k)
lemma reduced_1180 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1180 (a k) (relation_zero k)
lemma reduced_1181 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_1181 (a k) (relation_zero k)
lemma reduced_1182 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1182 (a k) (relation_zero k)
lemma reduced_1183 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1183 (a k) (relation_zero k)
lemma reduced_1184 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1184 (a k) (relation_zero k)
lemma reduced_1185 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  exact Universal.reduced_1185 (a k) (relation_zero k)
lemma reduced_1186 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_1186 (a k) (relation_zero k)
lemma reduced_1187 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_1187 (a k) (relation_zero k)
lemma reduced_1188 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_1188 (a k) (relation_zero k)
lemma reduced_1189 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_1189 (a k) (relation_zero k)
lemma reduced_1190 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_1190 (a k) (relation_zero k)
lemma reduced_1191 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_1191 (a k) (relation_zero k)
lemma reduced_1192 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_1192 (a k) (relation_zero k)
lemma reduced_1193 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_1193 (a k) (relation_zero k)
lemma reduced_1194 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_1194 (a k) (relation_zero k)
lemma reduced_1195 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_1195 (a k) (relation_zero k)
lemma reduced_1196 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_1196 (a k) (relation_zero k)
lemma reduced_1197 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_1197 (a k) (relation_zero k)
lemma reduced_1198 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_1198 (a k) (relation_zero k)
lemma reduced_1199 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_1199 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
