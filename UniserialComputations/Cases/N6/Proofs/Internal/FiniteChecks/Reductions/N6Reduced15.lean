import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_900 : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_900 v H)
lemma mul_reduced_900 (x : A) : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_900 v H)
lemma reduced_901 : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_901 v H)
lemma mul_reduced_901 (x : A) : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_901 v H)
lemma reduced_902 : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_902 v H)
lemma mul_reduced_902 (x : A) : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_902 v H)
lemma reduced_903 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_903 v H)
lemma mul_reduced_903 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_903 v H)
lemma reduced_904 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_904 v H)
lemma mul_reduced_904 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_904 v H)
lemma reduced_905 : word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_905 v H)
lemma mul_reduced_905 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_905 v H)
lemma reduced_906 : word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_906 v H)
lemma mul_reduced_906 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_906 v H)
lemma reduced_907 : word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_907 v H)
lemma mul_reduced_907 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_907 v H)
lemma reduced_908 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_908 v H)
lemma mul_reduced_908 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_908 v H)
lemma reduced_909 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_909 v H)
lemma mul_reduced_909 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_909 v H)
lemma reduced_910 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_910 v H)
lemma mul_reduced_910 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_910 v H)
lemma reduced_911 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_911 v H)
lemma mul_reduced_911 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_911 v H)
lemma reduced_912 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_912 v H)
lemma mul_reduced_912 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]*x=(word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_912 v H)
lemma reduced_913 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_913 v H)
lemma mul_reduced_913 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]*x=(word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_913 v H)
lemma reduced_914 : word v [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_914 v H)
lemma mul_reduced_914 (x : A) : word v [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_914 v H)
lemma reduced_915 : word v [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_915 v H)
lemma mul_reduced_915 (x : A) : word v [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_915 v H)
lemma reduced_916 : word v [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_916 v H)
lemma mul_reduced_916 (x : A) : word v [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_916 v H)
lemma reduced_917 : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_917 v H)
lemma mul_reduced_917 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_917 v H)
lemma reduced_918 : word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_918 v H)
lemma mul_reduced_918 (x : A) : word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]*x=(-(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_918 v H)
lemma reduced_919 : word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_919 v H)
lemma mul_reduced_919 (x : A) : word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]*x=(-(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_919 v H)
lemma reduced_920 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_920 v H)
lemma mul_reduced_920 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_920 v H)
lemma reduced_921 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_921 v H)
lemma mul_reduced_921 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_921 v H)
lemma reduced_922 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_922 v H)
lemma mul_reduced_922 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]*x=(word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_922 v H)
lemma reduced_923 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 62]=word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_923 v H)
lemma mul_reduced_923 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 62]*x=(word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_923 v H)
lemma reduced_924 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_924 v H)
lemma mul_reduced_924 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_924 v H)
lemma reduced_925 : word v [35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_925 v H)
lemma mul_reduced_925 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]*x=(word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_925 v H)
lemma reduced_926 : word v [52, 41, 43, 48, 51, 64, 36, 71, 72, 38, 28, 14]=(-word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_926 v H)
lemma mul_reduced_926 (x : A) : word v [52, 41, 43, 48, 51, 64, 36, 71, 72, 38, 28, 14]*x=(-(word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_926 v H)
lemma reduced_927 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_927 v H)
lemma mul_reduced_927 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]*x=(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_927 v H)
lemma reduced_928 : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_928 v H)
lemma mul_reduced_928 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]*x=(-(word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_928 v H)
lemma reduced_929 : word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_929 v H)
lemma mul_reduced_929 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]*x=(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_929 v H)
lemma reduced_930 : word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_930 v H)
lemma mul_reduced_930 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]*x=(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_930 v H)
lemma reduced_931 : word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 46]=word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_931 v H)
lemma mul_reduced_931 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 46]*x=(word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_931 v H)
lemma reduced_932 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48]=word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_932 v H)
lemma mul_reduced_932 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_932 v H)
lemma reduced_933 : word v [10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6]=word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_933 v H)
lemma mul_reduced_933 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_933 v H)
lemma reduced_934 : word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7]=word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_934 v H)
lemma mul_reduced_934 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_934 v H)
lemma reduced_935 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_935 v H)
lemma mul_reduced_935 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_935 v H)
lemma reduced_936 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]=word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_936 v H)
lemma mul_reduced_936 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]*x=(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_936 v H)
lemma reduced_937 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_937 v H)
lemma mul_reduced_937 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]*x=(word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_937 v H)
lemma reduced_938 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_938 v H)
lemma mul_reduced_938 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]*x=(word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_938 v H)
lemma reduced_939 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_939 v H)
lemma mul_reduced_939 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]*x=(word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_939 v H)
lemma reduced_940 : word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_940 v H)
lemma mul_reduced_940 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_940 v H)
lemma reduced_941 : word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_941 v H)
lemma mul_reduced_941 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_941 v H)
lemma reduced_942 : word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_942 v H)
lemma mul_reduced_942 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_942 v H)
lemma reduced_943 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 44]=word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_943 v H)
lemma mul_reduced_943 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 44]*x=(word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_943 v H)
lemma reduced_944 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_944 v H)
lemma mul_reduced_944 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_944 v H)
lemma reduced_945 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_945 v H)
lemma mul_reduced_945 (x : A) : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_945 v H)
lemma reduced_946 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_946 v H)
lemma mul_reduced_946 (x : A) : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_946 v H)
lemma reduced_947 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_947 v H)
lemma mul_reduced_947 (x : A) : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_947 v H)
lemma reduced_948 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4]=word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_948 v H)
lemma mul_reduced_948 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4]*x=(word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_948 v H)
lemma reduced_949 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_949 v H)
lemma mul_reduced_949 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]*x=(word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_949 v H)
lemma reduced_950 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_950 v H)
lemma mul_reduced_950 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]*x) + (word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_950 v H)
lemma reduced_951 : word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_951 v H)
lemma mul_reduced_951 (x : A) : word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_951 v H)
lemma reduced_952 : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_952 v H)
lemma mul_reduced_952 (x : A) : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_952 v H)
lemma reduced_953 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_953 v H)
lemma mul_reduced_953 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]*x=(-(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_953 v H)
lemma reduced_954 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_954 v H)
lemma mul_reduced_954 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]*x=(-(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_954 v H)
lemma reduced_955 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_955 v H)
lemma mul_reduced_955 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]*x=(word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_955 v H)
lemma reduced_956 : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_956 v H)
lemma mul_reduced_956 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]*x=(word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_956 v H)
lemma reduced_957 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_957 v H)
lemma mul_reduced_957 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]*x=(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_957 v H)
lemma reduced_958 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_958 v H)
lemma mul_reduced_958 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]*x=(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_958 v H)
lemma reduced_959 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_959 v H)
lemma mul_reduced_959 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_959 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_900 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_900 (a k) (relation_zero k)
lemma reduced_901 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.reduced_901 (a k) (relation_zero k)
lemma reduced_902 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_902 (a k) (relation_zero k)
lemma reduced_903 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_903 (a k) (relation_zero k)
lemma reduced_904 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_904 (a k) (relation_zero k)
lemma reduced_905 : word (a k) [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_905 (a k) (relation_zero k)
lemma reduced_906 : word (a k) [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_906 (a k) (relation_zero k)
lemma reduced_907 : word (a k) [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_907 (a k) (relation_zero k)
lemma reduced_908 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_908 (a k) (relation_zero k)
lemma reduced_909 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_909 (a k) (relation_zero k)
lemma reduced_910 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_910 (a k) (relation_zero k)
lemma reduced_911 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_911 (a k) (relation_zero k)
lemma reduced_912 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_912 (a k) (relation_zero k)
lemma reduced_913 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_913 (a k) (relation_zero k)
lemma reduced_914 : word (a k) [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_914 (a k) (relation_zero k)
lemma reduced_915 : word (a k) [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.reduced_915 (a k) (relation_zero k)
lemma reduced_916 : word (a k) [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_916 (a k) (relation_zero k)
lemma reduced_917 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_917 (a k) (relation_zero k)
lemma reduced_918 : word (a k) [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_918 (a k) (relation_zero k)
lemma reduced_919 : word (a k) [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_919 (a k) (relation_zero k)
lemma reduced_920 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_920 (a k) (relation_zero k)
lemma reduced_921 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_921 (a k) (relation_zero k)
lemma reduced_922 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_922 (a k) (relation_zero k)
lemma reduced_923 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 62]=word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_923 (a k) (relation_zero k)
lemma reduced_924 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.reduced_924 (a k) (relation_zero k)
lemma reduced_925 : word (a k) [35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_925 (a k) (relation_zero k)
lemma reduced_926 : word (a k) [52, 41, 43, 48, 51, 64, 36, 71, 72, 38, 28, 14]=(-word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18]) := by
  exact Universal.reduced_926 (a k) (relation_zero k)
lemma reduced_927 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  exact Universal.reduced_927 (a k) (relation_zero k)
lemma reduced_928 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_928 (a k) (relation_zero k)
lemma reduced_929 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_929 (a k) (relation_zero k)
lemma reduced_930 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_930 (a k) (relation_zero k)
lemma reduced_931 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 46]=word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43] := by
  exact Universal.reduced_931 (a k) (relation_zero k)
lemma reduced_932 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59] := by
  exact Universal.reduced_932 (a k) (relation_zero k)
lemma reduced_933 : word (a k) [10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47] := by
  exact Universal.reduced_933 (a k) (relation_zero k)
lemma reduced_934 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50] := by
  exact Universal.reduced_934 (a k) (relation_zero k)
lemma reduced_935 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_935 (a k) (relation_zero k)
lemma reduced_936 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]=word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  exact Universal.reduced_936 (a k) (relation_zero k)
lemma reduced_937 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_937 (a k) (relation_zero k)
lemma reduced_938 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_938 (a k) (relation_zero k)
lemma reduced_939 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_939 (a k) (relation_zero k)
lemma reduced_940 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_940 (a k) (relation_zero k)
lemma reduced_941 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_941 (a k) (relation_zero k)
lemma reduced_942 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_942 (a k) (relation_zero k)
lemma reduced_943 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 44]=word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27] := by
  exact Universal.reduced_943 (a k) (relation_zero k)
lemma reduced_944 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] := by
  exact Universal.reduced_944 (a k) (relation_zero k)
lemma reduced_945 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_945 (a k) (relation_zero k)
lemma reduced_946 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_946 (a k) (relation_zero k)
lemma reduced_947 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_947 (a k) (relation_zero k)
lemma reduced_948 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4]=word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_948 (a k) (relation_zero k)
lemma reduced_949 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_949 (a k) (relation_zero k)
lemma reduced_950 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  exact Universal.reduced_950 (a k) (relation_zero k)
lemma reduced_951 : word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_951 (a k) (relation_zero k)
lemma reduced_952 : word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.reduced_952 (a k) (relation_zero k)
lemma reduced_953 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_953 (a k) (relation_zero k)
lemma reduced_954 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_954 (a k) (relation_zero k)
lemma reduced_955 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_955 (a k) (relation_zero k)
lemma reduced_956 : word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_956 (a k) (relation_zero k)
lemma reduced_957 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_957 (a k) (relation_zero k)
lemma reduced_958 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_958 (a k) (relation_zero k)
lemma reduced_959 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_959 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
