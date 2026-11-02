import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_960 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_960 v H)
lemma mul_reduced_960 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_960 v H)
lemma reduced_961 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_961 v H)
lemma mul_reduced_961 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_961 v H)
lemma reduced_962 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_962 v H)
lemma mul_reduced_962 (x : A) : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_962 v H)
lemma reduced_963 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_963 v H)
lemma mul_reduced_963 (x : A) : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_963 v H)
lemma reduced_964 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_964 v H)
lemma mul_reduced_964 (x : A) : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_964 v H)
lemma reduced_965 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_965 v H)
lemma mul_reduced_965 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_965 v H)
lemma reduced_966 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_966 v H)
lemma mul_reduced_966 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_966 v H)
lemma reduced_967 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_967 v H)
lemma mul_reduced_967 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_967 v H)
lemma reduced_968 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_968 v H)
lemma mul_reduced_968 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_968 v H)
lemma reduced_969 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_969 v H)
lemma mul_reduced_969 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_969 v H)
lemma reduced_970 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_970 v H)
lemma mul_reduced_970 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_970 v H)
lemma reduced_971 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_971 v H)
lemma mul_reduced_971 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_971 v H)
lemma reduced_972 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_972 v H)
lemma mul_reduced_972 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_972 v H)
lemma reduced_973 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_973 v H)
lemma mul_reduced_973 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_973 v H)
lemma reduced_974 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_974 v H)
lemma mul_reduced_974 (x : A) : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_974 v H)
lemma reduced_975 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_975 v H)
lemma mul_reduced_975 (x : A) : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_975 v H)
lemma reduced_976 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_976 v H)
lemma mul_reduced_976 (x : A) : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_976 v H)
lemma reduced_977 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_977 v H)
lemma mul_reduced_977 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_977 v H)
lemma reduced_978 : word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_978 v H)
lemma mul_reduced_978 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_978 v H)
lemma reduced_979 : word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_979 v H)
lemma mul_reduced_979 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_979 v H)
lemma reduced_980 : word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_980 v H)
lemma mul_reduced_980 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_980 v H)
lemma reduced_981 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_981 v H)
lemma mul_reduced_981 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_981 v H)
lemma reduced_982 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_982 v H)
lemma mul_reduced_982 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_982 v H)
lemma reduced_983 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_983 v H)
lemma mul_reduced_983 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_983 v H)
lemma reduced_984 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_984 v H)
lemma mul_reduced_984 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_984 v H)
lemma reduced_985 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_985 v H)
lemma mul_reduced_985 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]*x=(word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_985 v H)
lemma reduced_986 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_986 v H)
lemma mul_reduced_986 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]*x=(word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_986 v H)
lemma reduced_987 : word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_987 v H)
lemma mul_reduced_987 (x : A) : word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_987 v H)
lemma reduced_988 : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_988 v H)
lemma mul_reduced_988 (x : A) : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_988 v H)
lemma reduced_989 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_989 v H)
lemma mul_reduced_989 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_989 v H)
lemma reduced_990 : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_990 v H)
lemma mul_reduced_990 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]*x=(-(word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_990 v H)
lemma reduced_991 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_991 v H)
lemma mul_reduced_991 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_991 v H)
lemma reduced_992 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_992 v H)
lemma mul_reduced_992 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_992 v H)
lemma reduced_993 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_993 v H)
lemma mul_reduced_993 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]*x=(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_993 v H)
lemma reduced_994 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_994 v H)
lemma mul_reduced_994 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]*x=(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_994 v H)
lemma reduced_995 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_995 v H)
lemma mul_reduced_995 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_995 v H)
lemma reduced_996 : word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_996 v H)
lemma mul_reduced_996 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]*x=(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_996 v H)
lemma reduced_997 : word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_997 v H)
lemma mul_reduced_997 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]*x=(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_997 v H)
lemma reduced_998 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_998 v H)
lemma mul_reduced_998 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_998 v H)
lemma reduced_999 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_999 v H)
lemma mul_reduced_999 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]*x=(-(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_999 v H)
lemma reduced_1000 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1000 v H)
lemma mul_reduced_1000 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]*x=(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1000 v H)
lemma reduced_1001 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1001 v H)
lemma mul_reduced_1001 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]*x=(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1001 v H)
lemma reduced_1002 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48]=word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1002 v H)
lemma mul_reduced_1002 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48]*x=(word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1002 v H)
lemma reduced_1003 : word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6]=word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1003 v H)
lemma mul_reduced_1003 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6]*x=(word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1003 v H)
lemma reduced_1004 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7]=word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1004 v H)
lemma mul_reduced_1004 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1004 v H)
lemma reduced_1005 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1005 v H)
lemma mul_reduced_1005 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1005 v H)
lemma reduced_1006 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]=word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1006 v H)
lemma mul_reduced_1006 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1006 v H)
lemma reduced_1007 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1007 v H)
lemma mul_reduced_1007 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]*x=(word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1007 v H)
lemma reduced_1008 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1008 v H)
lemma mul_reduced_1008 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]*x=(word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1008 v H)
lemma reduced_1009 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1009 v H)
lemma mul_reduced_1009 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1009 v H)
lemma reduced_1010 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1010 v H)
lemma mul_reduced_1010 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1010 v H)
lemma reduced_1011 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1011 v H)
lemma mul_reduced_1011 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1011 v H)
lemma reduced_1012 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1012 v H)
lemma mul_reduced_1012 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1012 v H)
lemma reduced_1013 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1013 v H)
lemma mul_reduced_1013 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1013 v H)
lemma reduced_1014 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1014 v H)
lemma mul_reduced_1014 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1014 v H)
lemma reduced_1015 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1015 v H)
lemma mul_reduced_1015 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1015 v H)
lemma reduced_1016 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1016 v H)
lemma mul_reduced_1016 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]*x=(word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1016 v H)
lemma reduced_1017 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4]=word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1017 v H)
lemma mul_reduced_1017 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4]*x=(word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1017 v H)
lemma reduced_1018 : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1018 v H)
lemma mul_reduced_1018 (x : A) : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1018 v H)
lemma reduced_1019 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_1019 v H)
lemma mul_reduced_1019 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]*x=(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]*x) + (word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_1019 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_960 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_960 (a k) (relation_zero k)
lemma reduced_961 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_961 (a k) (relation_zero k)
lemma reduced_962 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_962 (a k) (relation_zero k)
lemma reduced_963 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_963 (a k) (relation_zero k)
lemma reduced_964 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_964 (a k) (relation_zero k)
lemma reduced_965 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_965 (a k) (relation_zero k)
lemma reduced_966 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_966 (a k) (relation_zero k)
lemma reduced_967 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_967 (a k) (relation_zero k)
lemma reduced_968 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_968 (a k) (relation_zero k)
lemma reduced_969 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_969 (a k) (relation_zero k)
lemma reduced_970 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_970 (a k) (relation_zero k)
lemma reduced_971 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_971 (a k) (relation_zero k)
lemma reduced_972 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_972 (a k) (relation_zero k)
lemma reduced_973 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_973 (a k) (relation_zero k)
lemma reduced_974 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_974 (a k) (relation_zero k)
lemma reduced_975 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_975 (a k) (relation_zero k)
lemma reduced_976 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_976 (a k) (relation_zero k)
lemma reduced_977 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_977 (a k) (relation_zero k)
lemma reduced_978 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_978 (a k) (relation_zero k)
lemma reduced_979 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_979 (a k) (relation_zero k)
lemma reduced_980 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_980 (a k) (relation_zero k)
lemma reduced_981 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_981 (a k) (relation_zero k)
lemma reduced_982 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_982 (a k) (relation_zero k)
lemma reduced_983 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_983 (a k) (relation_zero k)
lemma reduced_984 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_984 (a k) (relation_zero k)
lemma reduced_985 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_985 (a k) (relation_zero k)
lemma reduced_986 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_986 (a k) (relation_zero k)
lemma reduced_987 : word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_987 (a k) (relation_zero k)
lemma reduced_988 : word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.reduced_988 (a k) (relation_zero k)
lemma reduced_989 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_989 (a k) (relation_zero k)
lemma reduced_990 : word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_990 (a k) (relation_zero k)
lemma reduced_991 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_991 (a k) (relation_zero k)
lemma reduced_992 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_992 (a k) (relation_zero k)
lemma reduced_993 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_993 (a k) (relation_zero k)
lemma reduced_994 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_994 (a k) (relation_zero k)
lemma reduced_995 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.reduced_995 (a k) (relation_zero k)
lemma reduced_996 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_996 (a k) (relation_zero k)
lemma reduced_997 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_997 (a k) (relation_zero k)
lemma reduced_998 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  exact Universal.reduced_998 (a k) (relation_zero k)
lemma reduced_999 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_999 (a k) (relation_zero k)
lemma reduced_1000 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_1000 (a k) (relation_zero k)
lemma reduced_1001 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_1001 (a k) (relation_zero k)
lemma reduced_1002 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48]=word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59] := by
  exact Universal.reduced_1002 (a k) (relation_zero k)
lemma reduced_1003 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6]=word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47] := by
  exact Universal.reduced_1003 (a k) (relation_zero k)
lemma reduced_1004 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50] := by
  exact Universal.reduced_1004 (a k) (relation_zero k)
lemma reduced_1005 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_1005 (a k) (relation_zero k)
lemma reduced_1006 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  exact Universal.reduced_1006 (a k) (relation_zero k)
lemma reduced_1007 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_1007 (a k) (relation_zero k)
lemma reduced_1008 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_1008 (a k) (relation_zero k)
lemma reduced_1009 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_1009 (a k) (relation_zero k)
lemma reduced_1010 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_1010 (a k) (relation_zero k)
lemma reduced_1011 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_1011 (a k) (relation_zero k)
lemma reduced_1012 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1012 (a k) (relation_zero k)
lemma reduced_1013 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] := by
  exact Universal.reduced_1013 (a k) (relation_zero k)
lemma reduced_1014 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1014 (a k) (relation_zero k)
lemma reduced_1015 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_1015 (a k) (relation_zero k)
lemma reduced_1016 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_1016 (a k) (relation_zero k)
lemma reduced_1017 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4]=word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_1017 (a k) (relation_zero k)
lemma reduced_1018 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_1018 (a k) (relation_zero k)
lemma reduced_1019 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  exact Universal.reduced_1019 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
