import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_840 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 62]=word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_840 v H)
lemma mul_reduced_840 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 62]*x=(word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_840 v H)
lemma reduced_841 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_841 v H)
lemma mul_reduced_841 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]*x=(word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_841 v H)
lemma reduced_842 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_842 v H)
lemma mul_reduced_842 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_842 v H)
lemma reduced_843 : word v [41, 43, 48, 51, 64, 36, 71, 72, 38, 28, 14]=(-word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_843 v H)
lemma mul_reduced_843 (x : A) : word v [41, 43, 48, 51, 64, 36, 71, 72, 38, 28, 14]*x=(-(word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_843 v H)
lemma reduced_844 : word v [55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_844 v H)
lemma mul_reduced_844 (x : A) : word v [55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]*x=(word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_844 v H)
lemma reduced_845 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_845 v H)
lemma mul_reduced_845 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_845 v H)
lemma reduced_846 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_846 v H)
lemma mul_reduced_846 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 54]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_846 v H)
lemma reduced_847 : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_847 v H)
lemma mul_reduced_847 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]*x=(-(word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_847 v H)
lemma reduced_848 : word v [35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_848 v H)
lemma mul_reduced_848 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]*x=(word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_848 v H)
lemma reduced_849 : word v [52, 41, 43, 48, 51, 64, 36, 71, 72, 38, 29]=(-word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_849 v H)
lemma mul_reduced_849 (x : A) : word v [52, 41, 43, 48, 51, 64, 36, 71, 72, 38, 29]*x=(-(word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_849 v H)
lemma reduced_850 : word v [10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 46]=word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_850 v H)
lemma mul_reduced_850 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 46]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_850 v H)
lemma reduced_851 : word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48]=word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_851 v H)
lemma mul_reduced_851 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_851 v H)
lemma reduced_852 : word v [11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6]=word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_852 v H)
lemma mul_reduced_852 (x : A) : word v [11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_852 v H)
lemma reduced_853 : word v [26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7]=word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_853 v H)
lemma mul_reduced_853 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7]*x=(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_853 v H)
lemma reduced_854 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_854 v H)
lemma mul_reduced_854 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_854 v H)
lemma reduced_855 : word v [31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]=word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_855 v H)
lemma mul_reduced_855 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_855 v H)
lemma reduced_856 : word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_856 v H)
lemma mul_reduced_856 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]*x=(word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_856 v H)
lemma reduced_857 : word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_857 v H)
lemma mul_reduced_857 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]*x=(word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_857 v H)
lemma reduced_858 : word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_858 v H)
lemma mul_reduced_858 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]*x=(word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_858 v H)
lemma reduced_859 : word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 41]=word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_859 v H)
lemma mul_reduced_859 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 41]*x=(word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_859 v H)
lemma reduced_860 : word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_860 v H)
lemma mul_reduced_860 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_860 v H)
lemma reduced_861 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 44]=word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_861 v H)
lemma mul_reduced_861 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 44]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_861 v H)
lemma reduced_862 : word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_862 v H)
lemma mul_reduced_862 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_862 v H)
lemma reduced_863 : word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_863 v H)
lemma mul_reduced_863 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_863 v H)
lemma reduced_864 : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_864 v H)
lemma mul_reduced_864 (x : A) : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_864 v H)
lemma reduced_865 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_865 v H)
lemma mul_reduced_865 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]*x=(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_865 v H)
lemma reduced_866 : word v [36, 70, 22, 3, 40, 60, 4, 54, 16, 57, 5]=word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_866 v H)
lemma mul_reduced_866 (x : A) : word v [36, 70, 22, 3, 40, 60, 4, 54, 16, 57, 5]*x=(word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_866 v H)
lemma reduced_867 : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_867 v H)
lemma mul_reduced_867 (x : A) : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_867 v H)
lemma reduced_868 : word v [27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_868 v H)
lemma mul_reduced_868 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]*x=(word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_868 v H)
lemma reduced_869 : word v [43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4]=word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_869 v H)
lemma mul_reduced_869 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4]*x=(word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_869 v H)
lemma reduced_870 : word v [45, 6, 7, 17, 21, 69, 8, 66, 25, 60, 4]=word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_870 v H)
lemma mul_reduced_870 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 25, 60, 4]*x=(word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_870 v H)
lemma reduced_871 : word v [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_871 v H)
lemma mul_reduced_871 (x : A) : word v [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_871 v H)
lemma reduced_872 : word v [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_872 v H)
lemma mul_reduced_872 (x : A) : word v [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_872 v H)
lemma reduced_873 : word v [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_873 v H)
lemma mul_reduced_873 (x : A) : word v [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_873 v H)
lemma reduced_874 : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_874 v H)
lemma mul_reduced_874 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]*x=(word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]*x) + (word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_874 v H)
lemma reduced_875 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_875 v H)
lemma mul_reduced_875 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]*x=(-(word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_875 v H)
lemma reduced_876 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 68, 40]=(-word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_876 v H)
lemma mul_reduced_876 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 68, 40]*x=(-(word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_876 v H)
lemma reduced_877 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_877 v H)
lemma mul_reduced_877 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]*x=(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_877 v H)
lemma reduced_878 : word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_878 v H)
lemma mul_reduced_878 (x : A) : word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]*x=(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_878 v H)
lemma reduced_879 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_879 v H)
lemma mul_reduced_879 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 73]*x=(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_879 v H)
lemma reduced_880 : word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_880 v H)
lemma mul_reduced_880 (x : A) : word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 23]*x=(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_880 v H)
lemma reduced_881 : word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_881 v H)
lemma mul_reduced_881 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]*x=(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_881 v H)
lemma reduced_882 : word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_882 v H)
lemma mul_reduced_882 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]*x=(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_882 v H)
lemma reduced_883 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_883 v H)
lemma mul_reduced_883 (x : A) : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_883 v H)
lemma reduced_884 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_884 v H)
lemma mul_reduced_884 (x : A) : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_884 v H)
lemma reduced_885 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_885 v H)
lemma mul_reduced_885 (x : A) : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_885 v H)
lemma reduced_886 : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_886 v H)
lemma mul_reduced_886 (x : A) : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_886 v H)
lemma reduced_887 : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_887 v H)
lemma mul_reduced_887 (x : A) : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_887 v H)
lemma reduced_888 : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_888 v H)
lemma mul_reduced_888 (x : A) : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_888 v H)
lemma reduced_889 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_889 v H)
lemma mul_reduced_889 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_889 v H)
lemma reduced_890 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_890 v H)
lemma mul_reduced_890 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_890 v H)
lemma reduced_891 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_891 v H)
lemma mul_reduced_891 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_891 v H)
lemma reduced_892 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_892 v H)
lemma mul_reduced_892 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_892 v H)
lemma reduced_893 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_893 v H)
lemma mul_reduced_893 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_893 v H)
lemma reduced_894 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_894 v H)
lemma mul_reduced_894 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_894 v H)
lemma reduced_895 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_895 v H)
lemma mul_reduced_895 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_895 v H)
lemma reduced_896 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_896 v H)
lemma mul_reduced_896 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_896 v H)
lemma reduced_897 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_897 v H)
lemma mul_reduced_897 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_897 v H)
lemma reduced_898 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_898 v H)
lemma mul_reduced_898 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_898 v H)
lemma reduced_899 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_899 v H)
lemma mul_reduced_899 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_899 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_840 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 62]=word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_840 (a k) (relation_zero k)
lemma reduced_841 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_841 (a k) (relation_zero k)
lemma reduced_842 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.reduced_842 (a k) (relation_zero k)
lemma reduced_843 : word (a k) [41, 43, 48, 51, 64, 36, 71, 72, 38, 28, 14]=(-word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18]) := by
  exact Universal.reduced_843 (a k) (relation_zero k)
lemma reduced_844 : word (a k) [55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_844 (a k) (relation_zero k)
lemma reduced_845 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  exact Universal.reduced_845 (a k) (relation_zero k)
lemma reduced_846 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  exact Universal.reduced_846 (a k) (relation_zero k)
lemma reduced_847 : word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_847 (a k) (relation_zero k)
lemma reduced_848 : word (a k) [35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_848 (a k) (relation_zero k)
lemma reduced_849 : word (a k) [52, 41, 43, 48, 51, 64, 36, 71, 72, 38, 29]=(-word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24]) := by
  exact Universal.reduced_849 (a k) (relation_zero k)
lemma reduced_850 : word (a k) [10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 46]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43] := by
  exact Universal.reduced_850 (a k) (relation_zero k)
lemma reduced_851 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59] := by
  exact Universal.reduced_851 (a k) (relation_zero k)
lemma reduced_852 : word (a k) [11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47] := by
  exact Universal.reduced_852 (a k) (relation_zero k)
lemma reduced_853 : word (a k) [26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7]=word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50] := by
  exact Universal.reduced_853 (a k) (relation_zero k)
lemma reduced_854 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_854 (a k) (relation_zero k)
lemma reduced_855 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  exact Universal.reduced_855 (a k) (relation_zero k)
lemma reduced_856 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_856 (a k) (relation_zero k)
lemma reduced_857 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_857 (a k) (relation_zero k)
lemma reduced_858 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_858 (a k) (relation_zero k)
lemma reduced_859 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 41]=word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56] := by
  exact Universal.reduced_859 (a k) (relation_zero k)
lemma reduced_860 : word (a k) [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_860 (a k) (relation_zero k)
lemma reduced_861 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 44]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27] := by
  exact Universal.reduced_861 (a k) (relation_zero k)
lemma reduced_862 : word (a k) [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_862 (a k) (relation_zero k)
lemma reduced_863 : word (a k) [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_863 (a k) (relation_zero k)
lemma reduced_864 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_864 (a k) (relation_zero k)
lemma reduced_865 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] := by
  exact Universal.reduced_865 (a k) (relation_zero k)
lemma reduced_866 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 16, 57, 5]=word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34] := by
  exact Universal.reduced_866 (a k) (relation_zero k)
lemma reduced_867 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_867 (a k) (relation_zero k)
lemma reduced_868 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_868 (a k) (relation_zero k)
lemma reduced_869 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4]=word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_869 (a k) (relation_zero k)
lemma reduced_870 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 25, 60, 4]=word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_870 (a k) (relation_zero k)
lemma reduced_871 : word (a k) [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_871 (a k) (relation_zero k)
lemma reduced_872 : word (a k) [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.reduced_872 (a k) (relation_zero k)
lemma reduced_873 : word (a k) [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_873 (a k) (relation_zero k)
lemma reduced_874 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  exact Universal.reduced_874 (a k) (relation_zero k)
lemma reduced_875 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_875 (a k) (relation_zero k)
lemma reduced_876 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 68, 40]=(-word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25]) := by
  exact Universal.reduced_876 (a k) (relation_zero k)
lemma reduced_877 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_877 (a k) (relation_zero k)
lemma reduced_878 : word (a k) [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_878 (a k) (relation_zero k)
lemma reduced_879 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_879 (a k) (relation_zero k)
lemma reduced_880 : word (a k) [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_880 (a k) (relation_zero k)
lemma reduced_881 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_881 (a k) (relation_zero k)
lemma reduced_882 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_882 (a k) (relation_zero k)
lemma reduced_883 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_883 (a k) (relation_zero k)
lemma reduced_884 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_884 (a k) (relation_zero k)
lemma reduced_885 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_885 (a k) (relation_zero k)
lemma reduced_886 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_886 (a k) (relation_zero k)
lemma reduced_887 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.reduced_887 (a k) (relation_zero k)
lemma reduced_888 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_888 (a k) (relation_zero k)
lemma reduced_889 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_889 (a k) (relation_zero k)
lemma reduced_890 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_890 (a k) (relation_zero k)
lemma reduced_891 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_891 (a k) (relation_zero k)
lemma reduced_892 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_892 (a k) (relation_zero k)
lemma reduced_893 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_893 (a k) (relation_zero k)
lemma reduced_894 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_894 (a k) (relation_zero k)
lemma reduced_895 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_895 (a k) (relation_zero k)
lemma reduced_896 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_896 (a k) (relation_zero k)
lemma reduced_897 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_897 (a k) (relation_zero k)
lemma reduced_898 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_898 (a k) (relation_zero k)
lemma reduced_899 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_899 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
