import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_780 : word v [13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_780 v H)
lemma mul_reduced_780 (x : A) : word v [13, 49, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_780 v H)
lemma reduced_781 : word v [17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_781 v H)
lemma mul_reduced_781 (x : A) : word v [17, 21, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_781 v H)
lemma reduced_782 : word v [63, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_782 v H)
lemma mul_reduced_782 (x : A) : word v [63, 21, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_782 v H)
lemma reduced_783 : word v [31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_783 v H)
lemma mul_reduced_783 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 59, 51]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_783 v H)
lemma reduced_784 : word v [69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_784 v H)
lemma mul_reduced_784 (x : A) : word v [69, 8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_784 v H)
lemma reduced_785 : word v [70, 22, 3, 40, 60, 4, 54, 16, 57, 5]=word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_785 v H)
lemma mul_reduced_785 (x : A) : word v [70, 22, 3, 40, 60, 4, 54, 16, 57, 5]*x=(word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_785 v H)
lemma reduced_786 : word v [6, 7, 17, 21, 69, 8, 66, 25, 60, 4]=word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_786 v H)
lemma mul_reduced_786 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 25, 60, 4]*x=(word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_786 v H)
lemma reduced_787 : word v [47, 7, 17, 21, 69, 8, 66, 25, 60, 4]=word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_787 v H)
lemma mul_reduced_787 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 25, 60, 4]*x=(word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_787 v H)
lemma reduced_788 : word v [58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_788 v H)
lemma mul_reduced_788 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 25, 60, 4]*x=(word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_788 v H)
lemma reduced_789 : word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 53]=word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_789 v H)
lemma mul_reduced_789 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 53]*x=(word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_789 v H)
lemma reduced_790 : word v [3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_790 v H)
lemma mul_reduced_790 (x : A) : word v [3, 40, 60, 4, 54, 15, 1, 34, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_790 v H)
lemma reduced_791 : word v [37, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_791 v H)
lemma mul_reduced_791 (x : A) : word v [37, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_791 v H)
lemma reduced_792 : word v [66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_792 v H)
lemma mul_reduced_792 (x : A) : word v [66, 24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_792 v H)
lemma reduced_793 : word v [67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_793 v H)
lemma mul_reduced_793 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 34, 64, 36]*x=(word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21]*x) + (word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_793 v H)
lemma reduced_794 : word v [41, 43, 47, 7, 17, 21, 69, 8, 68, 40]=(-word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_794 v H)
lemma mul_reduced_794 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 68, 40]*x=(-(word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_794 v H)
lemma reduced_795 : word v [55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_795 v H)
lemma mul_reduced_795 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 68, 40]*x=(-(word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_795 v H)
lemma reduced_796 : word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_796 v H)
lemma mul_reduced_796 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 73]*x=(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_796 v H)
lemma reduced_797 : word v [12, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_797 v H)
lemma mul_reduced_797 (x : A) : word v [12, 35, 55, 27, 58, 34, 63, 21, 70, 23]*x=(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_797 v H)
lemma reduced_798 : word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_798 v H)
lemma mul_reduced_798 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 73]*x=(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_798 v H)
lemma reduced_799 : word v [61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_799 v H)
lemma mul_reduced_799 (x : A) : word v [61, 35, 55, 27, 58, 34, 63, 21, 70, 23]*x=(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_799 v H)
lemma reduced_800 : word v [35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_800 v H)
lemma mul_reduced_800 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 71, 72, 37]*x=(word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_800 v H)
lemma reduced_801 : word v [52, 41, 43, 48, 51, 64, 36, 71, 72, 37]=(-word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_801 v H)
lemma mul_reduced_801 (x : A) : word v [52, 41, 43, 48, 51, 64, 36, 71, 72, 37]*x=(-(word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_801 v H)
lemma reduced_802 : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_802 v H)
lemma mul_reduced_802 (x : A) : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_802 v H)
lemma reduced_803 : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_803 v H)
lemma mul_reduced_803 (x : A) : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_803 v H)
lemma reduced_804 : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_804 v H)
lemma mul_reduced_804 (x : A) : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_804 v H)
lemma reduced_805 : word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_805 v H)
lemma mul_reduced_805 (x : A) : word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_805 v H)
lemma reduced_806 : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_806 v H)
lemma mul_reduced_806 (x : A) : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_806 v H)
lemma reduced_807 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_807 v H)
lemma mul_reduced_807 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_807 v H)
lemma reduced_808 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_808 v H)
lemma mul_reduced_808 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_808 v H)
lemma reduced_809 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_809 v H)
lemma mul_reduced_809 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_809 v H)
lemma reduced_810 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_810 v H)
lemma mul_reduced_810 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_810 v H)
lemma reduced_811 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_811 v H)
lemma mul_reduced_811 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_811 v H)
lemma reduced_812 : word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_812 v H)
lemma mul_reduced_812 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_812 v H)
lemma reduced_813 : word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_813 v H)
lemma mul_reduced_813 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_813 v H)
lemma reduced_814 : word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_814 v H)
lemma mul_reduced_814 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_814 v H)
lemma reduced_815 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_815 v H)
lemma mul_reduced_815 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_815 v H)
lemma reduced_816 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_816 v H)
lemma mul_reduced_816 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_816 v H)
lemma reduced_817 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_817 v H)
lemma mul_reduced_817 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_817 v H)
lemma reduced_818 : word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_818 v H)
lemma mul_reduced_818 (x : A) : word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_818 v H)
lemma reduced_819 : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_819 v H)
lemma mul_reduced_819 (x : A) : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_819 v H)
lemma reduced_820 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_820 v H)
lemma mul_reduced_820 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_820 v H)
lemma reduced_821 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_821 v H)
lemma mul_reduced_821 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_821 v H)
lemma reduced_822 : word v [13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_822 v H)
lemma mul_reduced_822 (x : A) : word v [13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_822 v H)
lemma reduced_823 : word v [17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_823 v H)
lemma mul_reduced_823 (x : A) : word v [17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_823 v H)
lemma reduced_824 : word v [63, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_824 v H)
lemma mul_reduced_824 (x : A) : word v [63, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_824 v H)
lemma reduced_825 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_825 v H)
lemma mul_reduced_825 (x : A) : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_825 v H)
lemma reduced_826 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_826 v H)
lemma mul_reduced_826 (x : A) : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_826 v H)
lemma reduced_827 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_827 v H)
lemma mul_reduced_827 (x : A) : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_827 v H)
lemma reduced_828 : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_828 v H)
lemma mul_reduced_828 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_828 v H)
lemma reduced_829 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_829 v H)
lemma mul_reduced_829 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]*x=(word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_829 v H)
lemma reduced_830 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_830 v H)
lemma mul_reduced_830 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]*x=(word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_830 v H)
lemma reduced_831 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 52]=word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_831 v H)
lemma mul_reduced_831 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 52]*x=(word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_831 v H)
lemma reduced_832 : word v [3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_832 v H)
lemma mul_reduced_832 (x : A) : word v [3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_832 v H)
lemma reduced_833 : word v [37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_833 v H)
lemma mul_reduced_833 (x : A) : word v [37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_833 v H)
lemma reduced_834 : word v [66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_834 v H)
lemma mul_reduced_834 (x : A) : word v [66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_834 v H)
lemma reduced_835 : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_835 v H)
lemma mul_reduced_835 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_835 v H)
lemma reduced_836 : word v [12, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_836 v H)
lemma mul_reduced_836 (x : A) : word v [12, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]*x=(-(word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_836 v H)
lemma reduced_837 : word v [61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_837 v H)
lemma mul_reduced_837 (x : A) : word v [61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]*x=(-(word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_837 v H)
lemma reduced_838 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_838 v H)
lemma mul_reduced_838 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_838 v H)
lemma reduced_839 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_839 v H)
lemma mul_reduced_839 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_839 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_780 : word (a k) [13, 49, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_780 (a k) (relation_zero k)
lemma reduced_781 : word (a k) [17, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_781 (a k) (relation_zero k)
lemma reduced_782 : word (a k) [63, 21, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_782 (a k) (relation_zero k)
lemma reduced_783 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34] := by
  exact Universal.reduced_783 (a k) (relation_zero k)
lemma reduced_784 : word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_784 (a k) (relation_zero k)
lemma reduced_785 : word (a k) [70, 22, 3, 40, 60, 4, 54, 16, 57, 5]=word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1, 34] := by
  exact Universal.reduced_785 (a k) (relation_zero k)
lemma reduced_786 : word (a k) [6, 7, 17, 21, 69, 8, 66, 25, 60, 4]=word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_786 (a k) (relation_zero k)
lemma reduced_787 : word (a k) [47, 7, 17, 21, 69, 8, 66, 25, 60, 4]=word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_787 (a k) (relation_zero k)
lemma reduced_788 : word (a k) [58, 33, 13, 49, 69, 8, 66, 25, 60, 4]=word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_788 (a k) (relation_zero k)
lemma reduced_789 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 62, 53]=word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35] := by
  exact Universal.reduced_789 (a k) (relation_zero k)
lemma reduced_790 : word (a k) [3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.reduced_790 (a k) (relation_zero k)
lemma reduced_791 : word (a k) [37, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_791 (a k) (relation_zero k)
lemma reduced_792 : word (a k) [66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_792 (a k) (relation_zero k)
lemma reduced_793 : word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 64, 36]=word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  exact Universal.reduced_793 (a k) (relation_zero k)
lemma reduced_794 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 68, 40]=(-word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 25]) := by
  exact Universal.reduced_794 (a k) (relation_zero k)
lemma reduced_795 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_795 (a k) (relation_zero k)
lemma reduced_796 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_796 (a k) (relation_zero k)
lemma reduced_797 : word (a k) [12, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_797 (a k) (relation_zero k)
lemma reduced_798 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_798 (a k) (relation_zero k)
lemma reduced_799 : word (a k) [61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_799 (a k) (relation_zero k)
lemma reduced_800 : word (a k) [35, 55, 27, 58, 33, 13, 49, 71, 72, 37]=word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_800 (a k) (relation_zero k)
lemma reduced_801 : word (a k) [52, 41, 43, 48, 51, 64, 36, 71, 72, 37]=(-word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66]) := by
  exact Universal.reduced_801 (a k) (relation_zero k)
lemma reduced_802 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_802 (a k) (relation_zero k)
lemma reduced_803 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  exact Universal.reduced_803 (a k) (relation_zero k)
lemma reduced_804 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_804 (a k) (relation_zero k)
lemma reduced_805 : word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_805 (a k) (relation_zero k)
lemma reduced_806 : word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.reduced_806 (a k) (relation_zero k)
lemma reduced_807 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_807 (a k) (relation_zero k)
lemma reduced_808 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_808 (a k) (relation_zero k)
lemma reduced_809 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_809 (a k) (relation_zero k)
lemma reduced_810 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_810 (a k) (relation_zero k)
lemma reduced_811 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_811 (a k) (relation_zero k)
lemma reduced_812 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_812 (a k) (relation_zero k)
lemma reduced_813 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_813 (a k) (relation_zero k)
lemma reduced_814 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_814 (a k) (relation_zero k)
lemma reduced_815 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_815 (a k) (relation_zero k)
lemma reduced_816 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_816 (a k) (relation_zero k)
lemma reduced_817 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_817 (a k) (relation_zero k)
lemma reduced_818 : word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_818 (a k) (relation_zero k)
lemma reduced_819 : word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.reduced_819 (a k) (relation_zero k)
lemma reduced_820 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_820 (a k) (relation_zero k)
lemma reduced_821 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_821 (a k) (relation_zero k)
lemma reduced_822 : word (a k) [13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_822 (a k) (relation_zero k)
lemma reduced_823 : word (a k) [17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_823 (a k) (relation_zero k)
lemma reduced_824 : word (a k) [63, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_824 (a k) (relation_zero k)
lemma reduced_825 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_825 (a k) (relation_zero k)
lemma reduced_826 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_826 (a k) (relation_zero k)
lemma reduced_827 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_827 (a k) (relation_zero k)
lemma reduced_828 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_828 (a k) (relation_zero k)
lemma reduced_829 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_829 (a k) (relation_zero k)
lemma reduced_830 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_830 (a k) (relation_zero k)
lemma reduced_831 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 52]=word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_831 (a k) (relation_zero k)
lemma reduced_832 : word (a k) [3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.reduced_832 (a k) (relation_zero k)
lemma reduced_833 : word (a k) [37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_833 (a k) (relation_zero k)
lemma reduced_834 : word (a k) [66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_834 (a k) (relation_zero k)
lemma reduced_835 : word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_835 (a k) (relation_zero k)
lemma reduced_836 : word (a k) [12, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_836 (a k) (relation_zero k)
lemma reduced_837 : word (a k) [61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_837 (a k) (relation_zero k)
lemma reduced_838 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_838 (a k) (relation_zero k)
lemma reduced_839 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_839 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
