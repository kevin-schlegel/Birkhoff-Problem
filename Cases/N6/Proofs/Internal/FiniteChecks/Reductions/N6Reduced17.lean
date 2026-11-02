import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_1020 : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1020 v H)
lemma mul_reduced_1020 (x : A) : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1020 v H)
lemma reduced_1021 : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1021 v H)
lemma mul_reduced_1021 (x : A) : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1021 v H)
lemma reduced_1022 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1022 v H)
lemma mul_reduced_1022 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]*x=(-(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1022 v H)
lemma reduced_1023 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1023 v H)
lemma mul_reduced_1023 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]*x=(-(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1023 v H)
lemma reduced_1024 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1024 v H)
lemma mul_reduced_1024 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]*x=(word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1024 v H)
lemma reduced_1025 : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1025 v H)
lemma mul_reduced_1025 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]*x=(word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1025 v H)
lemma reduced_1026 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1026 v H)
lemma mul_reduced_1026 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]*x=(word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1026 v H)
lemma reduced_1027 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1027 v H)
lemma mul_reduced_1027 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1027 v H)
lemma reduced_1028 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1028 v H)
lemma mul_reduced_1028 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1028 v H)
lemma reduced_1029 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1029 v H)
lemma mul_reduced_1029 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1029 v H)
lemma reduced_1030 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1030 v H)
lemma mul_reduced_1030 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1030 v H)
lemma reduced_1031 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1031 v H)
lemma mul_reduced_1031 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1031 v H)
lemma reduced_1032 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1032 v H)
lemma mul_reduced_1032 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1032 v H)
lemma reduced_1033 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1033 v H)
lemma mul_reduced_1033 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1033 v H)
lemma reduced_1034 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1034 v H)
lemma mul_reduced_1034 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1034 v H)
lemma reduced_1035 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1035 v H)
lemma mul_reduced_1035 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1035 v H)
lemma reduced_1036 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1036 v H)
lemma mul_reduced_1036 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1036 v H)
lemma reduced_1037 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1037 v H)
lemma mul_reduced_1037 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1037 v H)
lemma reduced_1038 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1038 v H)
lemma mul_reduced_1038 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1038 v H)
lemma reduced_1039 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1039 v H)
lemma mul_reduced_1039 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1039 v H)
lemma reduced_1040 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1040 v H)
lemma mul_reduced_1040 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1040 v H)
lemma reduced_1041 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1041 v H)
lemma mul_reduced_1041 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1041 v H)
lemma reduced_1042 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1042 v H)
lemma mul_reduced_1042 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1042 v H)
lemma reduced_1043 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1043 v H)
lemma mul_reduced_1043 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1043 v H)
lemma reduced_1044 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1044 v H)
lemma mul_reduced_1044 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1044 v H)
lemma reduced_1045 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1045 v H)
lemma mul_reduced_1045 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1045 v H)
lemma reduced_1046 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1046 v H)
lemma mul_reduced_1046 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1046 v H)
lemma reduced_1047 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1047 v H)
lemma mul_reduced_1047 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1047 v H)
lemma reduced_1048 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1048 v H)
lemma mul_reduced_1048 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1048 v H)
lemma reduced_1049 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1049 v H)
lemma mul_reduced_1049 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1049 v H)
lemma reduced_1050 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1050 v H)
lemma mul_reduced_1050 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1050 v H)
lemma reduced_1051 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1051 v H)
lemma mul_reduced_1051 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]*x=(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1051 v H)
lemma reduced_1052 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1052 v H)
lemma mul_reduced_1052 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]*x=(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1052 v H)
lemma reduced_1053 : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1053 v H)
lemma mul_reduced_1053 (x : A) : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1053 v H)
lemma reduced_1054 : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1054 v H)
lemma mul_reduced_1054 (x : A) : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1054 v H)
lemma reduced_1055 : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1055 v H)
lemma mul_reduced_1055 (x : A) : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1055 v H)
lemma reduced_1056 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1056 v H)
lemma mul_reduced_1056 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1056 v H)
lemma reduced_1057 : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1057 v H)
lemma mul_reduced_1057 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]*x=(-(word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1057 v H)
lemma reduced_1058 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1058 v H)
lemma mul_reduced_1058 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1058 v H)
lemma reduced_1059 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1059 v H)
lemma mul_reduced_1059 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1059 v H)
lemma reduced_1060 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1060 v H)
lemma mul_reduced_1060 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]*x=(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1060 v H)
lemma reduced_1061 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1061 v H)
lemma mul_reduced_1061 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]*x=(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1061 v H)
lemma reduced_1062 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1062 v H)
lemma mul_reduced_1062 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]*x=(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1062 v H)
lemma reduced_1063 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1063 v H)
lemma mul_reduced_1063 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]*x=(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1063 v H)
lemma reduced_1064 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1064 v H)
lemma mul_reduced_1064 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1064 v H)
lemma reduced_1065 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1065 v H)
lemma mul_reduced_1065 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]*x=(-(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1065 v H)
lemma reduced_1066 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1066 v H)
lemma mul_reduced_1066 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]*x=(word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1066 v H)
lemma reduced_1067 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7]=word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1067 v H)
lemma mul_reduced_1067 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7]*x=(word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1067 v H)
lemma reduced_1068 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1068 v H)
lemma mul_reduced_1068 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1068 v H)
lemma reduced_1069 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]=word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1069 v H)
lemma mul_reduced_1069 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1069 v H)
lemma reduced_1070 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1070 v H)
lemma mul_reduced_1070 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]*x=(word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1070 v H)
lemma reduced_1071 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1071 v H)
lemma mul_reduced_1071 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]*x=(word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1071 v H)
lemma reduced_1072 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1072 v H)
lemma mul_reduced_1072 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1072 v H)
lemma reduced_1073 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1073 v H)
lemma mul_reduced_1073 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1073 v H)
lemma reduced_1074 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1074 v H)
lemma mul_reduced_1074 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1074 v H)
lemma reduced_1075 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1075 v H)
lemma mul_reduced_1075 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1075 v H)
lemma reduced_1076 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1076 v H)
lemma mul_reduced_1076 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1076 v H)
lemma reduced_1077 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1077 v H)
lemma mul_reduced_1077 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]*x=(word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1077 v H)
lemma reduced_1078 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1078 v H)
lemma mul_reduced_1078 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]*x=(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1078 v H)
lemma reduced_1079 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1079 v H)
lemma mul_reduced_1079 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]*x=(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1079 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_1020 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.reduced_1020 (a k) (relation_zero k)
lemma reduced_1021 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1021 (a k) (relation_zero k)
lemma reduced_1022 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_1022 (a k) (relation_zero k)
lemma reduced_1023 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_1023 (a k) (relation_zero k)
lemma reduced_1024 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_1024 (a k) (relation_zero k)
lemma reduced_1025 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_1025 (a k) (relation_zero k)
lemma reduced_1026 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_1026 (a k) (relation_zero k)
lemma reduced_1027 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_1027 (a k) (relation_zero k)
lemma reduced_1028 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_1028 (a k) (relation_zero k)
lemma reduced_1029 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_1029 (a k) (relation_zero k)
lemma reduced_1030 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_1030 (a k) (relation_zero k)
lemma reduced_1031 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_1031 (a k) (relation_zero k)
lemma reduced_1032 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_1032 (a k) (relation_zero k)
lemma reduced_1033 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_1033 (a k) (relation_zero k)
lemma reduced_1034 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_1034 (a k) (relation_zero k)
lemma reduced_1035 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_1035 (a k) (relation_zero k)
lemma reduced_1036 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_1036 (a k) (relation_zero k)
lemma reduced_1037 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_1037 (a k) (relation_zero k)
lemma reduced_1038 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_1038 (a k) (relation_zero k)
lemma reduced_1039 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_1039 (a k) (relation_zero k)
lemma reduced_1040 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_1040 (a k) (relation_zero k)
lemma reduced_1041 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_1041 (a k) (relation_zero k)
lemma reduced_1042 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_1042 (a k) (relation_zero k)
lemma reduced_1043 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_1043 (a k) (relation_zero k)
lemma reduced_1044 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_1044 (a k) (relation_zero k)
lemma reduced_1045 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_1045 (a k) (relation_zero k)
lemma reduced_1046 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_1046 (a k) (relation_zero k)
lemma reduced_1047 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_1047 (a k) (relation_zero k)
lemma reduced_1048 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_1048 (a k) (relation_zero k)
lemma reduced_1049 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_1049 (a k) (relation_zero k)
lemma reduced_1050 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_1050 (a k) (relation_zero k)
lemma reduced_1051 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_1051 (a k) (relation_zero k)
lemma reduced_1052 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_1052 (a k) (relation_zero k)
lemma reduced_1053 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1053 (a k) (relation_zero k)
lemma reduced_1054 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.reduced_1054 (a k) (relation_zero k)
lemma reduced_1055 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_1055 (a k) (relation_zero k)
lemma reduced_1056 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_1056 (a k) (relation_zero k)
lemma reduced_1057 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_1057 (a k) (relation_zero k)
lemma reduced_1058 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_1058 (a k) (relation_zero k)
lemma reduced_1059 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_1059 (a k) (relation_zero k)
lemma reduced_1060 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_1060 (a k) (relation_zero k)
lemma reduced_1061 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_1061 (a k) (relation_zero k)
lemma reduced_1062 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_1062 (a k) (relation_zero k)
lemma reduced_1063 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_1063 (a k) (relation_zero k)
lemma reduced_1064 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  exact Universal.reduced_1064 (a k) (relation_zero k)
lemma reduced_1065 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_1065 (a k) (relation_zero k)
lemma reduced_1066 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_1066 (a k) (relation_zero k)
lemma reduced_1067 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7]=word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50] := by
  exact Universal.reduced_1067 (a k) (relation_zero k)
lemma reduced_1068 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_1068 (a k) (relation_zero k)
lemma reduced_1069 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  exact Universal.reduced_1069 (a k) (relation_zero k)
lemma reduced_1070 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_1070 (a k) (relation_zero k)
lemma reduced_1071 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_1071 (a k) (relation_zero k)
lemma reduced_1072 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_1072 (a k) (relation_zero k)
lemma reduced_1073 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_1073 (a k) (relation_zero k)
lemma reduced_1074 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1074 (a k) (relation_zero k)
lemma reduced_1075 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1075 (a k) (relation_zero k)
lemma reduced_1076 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1076 (a k) (relation_zero k)
lemma reduced_1077 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] := by
  exact Universal.reduced_1077 (a k) (relation_zero k)
lemma reduced_1078 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_1078 (a k) (relation_zero k)
lemma reduced_1079 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_1079 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
