import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_1200 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1200 v H)
lemma mul_reduced_1200 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1200 v H)
lemma reduced_1201 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1201 v H)
lemma mul_reduced_1201 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1201 v H)
lemma reduced_1202 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1202 v H)
lemma mul_reduced_1202 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1202 v H)
lemma reduced_1203 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1203 v H)
lemma mul_reduced_1203 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1203 v H)
lemma reduced_1204 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1204 v H)
lemma mul_reduced_1204 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1204 v H)
lemma reduced_1205 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1205 v H)
lemma mul_reduced_1205 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1205 v H)
lemma reduced_1206 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1206 v H)
lemma mul_reduced_1206 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]*x=(word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1206 v H)
lemma reduced_1207 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1207 v H)
lemma mul_reduced_1207 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1207 v H)
lemma reduced_1208 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1208 v H)
lemma mul_reduced_1208 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1208 v H)
lemma reduced_1209 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1209 v H)
lemma mul_reduced_1209 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1209 v H)
lemma reduced_1210 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1210 v H)
lemma mul_reduced_1210 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1210 v H)
lemma reduced_1211 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1211 v H)
lemma mul_reduced_1211 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]*x=(-(word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1211 v H)
lemma reduced_1212 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1212 v H)
lemma mul_reduced_1212 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1212 v H)
lemma reduced_1213 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1213 v H)
lemma mul_reduced_1213 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1213 v H)
lemma reduced_1214 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1214 v H)
lemma mul_reduced_1214 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1214 v H)
lemma reduced_1215 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1215 v H)
lemma mul_reduced_1215 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]*x=(-(word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1215 v H)
lemma reduced_1216 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1216 v H)
lemma mul_reduced_1216 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]*x=(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1216 v H)
lemma reduced_1217 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1217 v H)
lemma mul_reduced_1217 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1217 v H)
lemma reduced_1218 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1218 v H)
lemma mul_reduced_1218 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]*x=(word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1218 v H)
lemma reduced_1219 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1219 v H)
lemma mul_reduced_1219 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1219 v H)
lemma reduced_1220 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1220 v H)
lemma mul_reduced_1220 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1220 v H)
lemma reduced_1221 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1221 v H)
lemma mul_reduced_1221 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1221 v H)
lemma reduced_1222 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1222 v H)
lemma mul_reduced_1222 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1222 v H)
lemma reduced_1223 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1223 v H)
lemma mul_reduced_1223 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]*x=(word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1223 v H)
lemma reduced_1224 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1224 v H)
lemma mul_reduced_1224 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1224 v H)
lemma reduced_1225 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1225 v H)
lemma mul_reduced_1225 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1225 v H)
lemma reduced_1226 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1226 v H)
lemma mul_reduced_1226 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1226 v H)
lemma reduced_1227 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1227 v H)
lemma mul_reduced_1227 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]*x=(-(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1227 v H)
lemma reduced_1228 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1228 v H)
lemma mul_reduced_1228 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1228 v H)
lemma reduced_1229 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1229 v H)
lemma mul_reduced_1229 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1229 v H)
lemma reduced_1230 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1230 v H)
lemma mul_reduced_1230 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1230 v H)
lemma reduced_1231 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1231 v H)
lemma mul_reduced_1231 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1231 v H)
lemma reduced_1232 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1232 v H)
lemma mul_reduced_1232 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1232 v H)
lemma reduced_1233 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1233 v H)
lemma mul_reduced_1233 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1233 v H)
lemma reduced_1234 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1234 v H)
lemma mul_reduced_1234 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1234 v H)
lemma reduced_1235 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1235 v H)
lemma mul_reduced_1235 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1235 v H)
lemma reduced_1236 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1236 v H)
lemma mul_reduced_1236 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1236 v H)
lemma reduced_1237 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1237 v H)
lemma mul_reduced_1237 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1237 v H)
lemma reduced_1238 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1238 v H)
lemma mul_reduced_1238 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1238 v H)
lemma reduced_1239 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1239 v H)
lemma mul_reduced_1239 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1239 v H)
lemma reduced_1240 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1240 v H)
lemma mul_reduced_1240 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1240 v H)
lemma reduced_1241 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1241 v H)
lemma mul_reduced_1241 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1241 v H)
lemma reduced_1242 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1242 v H)
lemma mul_reduced_1242 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1242 v H)
lemma reduced_1243 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1243 v H)
lemma mul_reduced_1243 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1243 v H)
lemma reduced_1244 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1244 v H)
lemma mul_reduced_1244 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1244 v H)
lemma reduced_1245 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1245 v H)
lemma mul_reduced_1245 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1245 v H)
lemma reduced_1246 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1246 v H)
lemma mul_reduced_1246 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1246 v H)
lemma reduced_1247 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1247 v H)
lemma mul_reduced_1247 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1247 v H)
lemma reduced_1248 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1248 v H)
lemma mul_reduced_1248 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1248 v H)
lemma reduced_1249 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1249 v H)
lemma mul_reduced_1249 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1249 v H)
lemma reduced_1250 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1250 v H)
lemma mul_reduced_1250 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]*x=(-(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1250 v H)
lemma reduced_1251 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1251 v H)
lemma mul_reduced_1251 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1251 v H)
lemma reduced_1252 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1252 v H)
lemma mul_reduced_1252 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]*x=(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1252 v H)
lemma reduced_1253 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1253 v H)
lemma mul_reduced_1253 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]*x=(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1253 v H)
lemma reduced_1254 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1254 v H)
lemma mul_reduced_1254 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1254 v H)
lemma reduced_1255 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1255 v H)
lemma mul_reduced_1255 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]*x=(word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1255 v H)
lemma reduced_1256 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1256 v H)
lemma mul_reduced_1256 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1256 v H)
lemma reduced_1257 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1257 v H)
lemma mul_reduced_1257 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1257 v H)
lemma reduced_1258 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1258 v H)
lemma mul_reduced_1258 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1258 v H)
lemma reduced_1259 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1259 v H)
lemma mul_reduced_1259 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1259 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_1200 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_1200 (a k) (relation_zero k)
lemma reduced_1201 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_1201 (a k) (relation_zero k)
lemma reduced_1202 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_1202 (a k) (relation_zero k)
lemma reduced_1203 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_1203 (a k) (relation_zero k)
lemma reduced_1204 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_1204 (a k) (relation_zero k)
lemma reduced_1205 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_1205 (a k) (relation_zero k)
lemma reduced_1206 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_1206 (a k) (relation_zero k)
lemma reduced_1207 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1207 (a k) (relation_zero k)
lemma reduced_1208 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1208 (a k) (relation_zero k)
lemma reduced_1209 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1209 (a k) (relation_zero k)
lemma reduced_1210 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_1210 (a k) (relation_zero k)
lemma reduced_1211 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_1211 (a k) (relation_zero k)
lemma reduced_1212 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_1212 (a k) (relation_zero k)
lemma reduced_1213 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_1213 (a k) (relation_zero k)
lemma reduced_1214 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_1214 (a k) (relation_zero k)
lemma reduced_1215 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_1215 (a k) (relation_zero k)
lemma reduced_1216 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_1216 (a k) (relation_zero k)
lemma reduced_1217 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_1217 (a k) (relation_zero k)
lemma reduced_1218 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_1218 (a k) (relation_zero k)
lemma reduced_1219 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_1219 (a k) (relation_zero k)
lemma reduced_1220 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_1220 (a k) (relation_zero k)
lemma reduced_1221 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1221 (a k) (relation_zero k)
lemma reduced_1222 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1222 (a k) (relation_zero k)
lemma reduced_1223 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_1223 (a k) (relation_zero k)
lemma reduced_1224 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1224 (a k) (relation_zero k)
lemma reduced_1225 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1225 (a k) (relation_zero k)
lemma reduced_1226 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1226 (a k) (relation_zero k)
lemma reduced_1227 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_1227 (a k) (relation_zero k)
lemma reduced_1228 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_1228 (a k) (relation_zero k)
lemma reduced_1229 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_1229 (a k) (relation_zero k)
lemma reduced_1230 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_1230 (a k) (relation_zero k)
lemma reduced_1231 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_1231 (a k) (relation_zero k)
lemma reduced_1232 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_1232 (a k) (relation_zero k)
lemma reduced_1233 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_1233 (a k) (relation_zero k)
lemma reduced_1234 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_1234 (a k) (relation_zero k)
lemma reduced_1235 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_1235 (a k) (relation_zero k)
lemma reduced_1236 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_1236 (a k) (relation_zero k)
lemma reduced_1237 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_1237 (a k) (relation_zero k)
lemma reduced_1238 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_1238 (a k) (relation_zero k)
lemma reduced_1239 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_1239 (a k) (relation_zero k)
lemma reduced_1240 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_1240 (a k) (relation_zero k)
lemma reduced_1241 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_1241 (a k) (relation_zero k)
lemma reduced_1242 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_1242 (a k) (relation_zero k)
lemma reduced_1243 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_1243 (a k) (relation_zero k)
lemma reduced_1244 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_1244 (a k) (relation_zero k)
lemma reduced_1245 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_1245 (a k) (relation_zero k)
lemma reduced_1246 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_1246 (a k) (relation_zero k)
lemma reduced_1247 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1247 (a k) (relation_zero k)
lemma reduced_1248 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1248 (a k) (relation_zero k)
lemma reduced_1249 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1249 (a k) (relation_zero k)
lemma reduced_1250 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_1250 (a k) (relation_zero k)
lemma reduced_1251 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_1251 (a k) (relation_zero k)
lemma reduced_1252 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_1252 (a k) (relation_zero k)
lemma reduced_1253 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_1253 (a k) (relation_zero k)
lemma reduced_1254 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_1254 (a k) (relation_zero k)
lemma reduced_1255 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_1255 (a k) (relation_zero k)
lemma reduced_1256 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_1256 (a k) (relation_zero k)
lemma reduced_1257 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1257 (a k) (relation_zero k)
lemma reduced_1258 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1258 (a k) (relation_zero k)
lemma reduced_1259 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_1259 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
