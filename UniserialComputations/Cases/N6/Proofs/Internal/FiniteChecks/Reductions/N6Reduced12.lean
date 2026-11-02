import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_720 : word v [55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_720 v H)
lemma mul_reduced_720 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_720 v H)
lemma reduced_721 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_721 v H)
lemma mul_reduced_721 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_721 v H)
lemma reduced_722 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_722 v H)
lemma mul_reduced_722 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_722 v H)
lemma reduced_723 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_723 v H)
lemma mul_reduced_723 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_723 v H)
lemma reduced_724 : word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_724 v H)
lemma mul_reduced_724 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_724 v H)
lemma reduced_725 : word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_725 v H)
lemma mul_reduced_725 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_725 v H)
lemma reduced_726 : word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_726 v H)
lemma mul_reduced_726 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_726 v H)
lemma reduced_727 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_727 v H)
lemma mul_reduced_727 (x : A) : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_727 v H)
lemma reduced_728 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_728 v H)
lemma mul_reduced_728 (x : A) : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_728 v H)
lemma reduced_729 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_729 v H)
lemma mul_reduced_729 (x : A) : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_729 v H)
lemma reduced_730 : word v [8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_730 v H)
lemma mul_reduced_730 (x : A) : word v [8, 66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_730 v H)
lemma reduced_731 : word v [22, 3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_731 v H)
lemma mul_reduced_731 (x : A) : word v [22, 3, 40, 60, 4, 54, 15, 1, 34, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_731 v H)
lemma reduced_732 : word v [72, 37, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_732 v H)
lemma mul_reduced_732 (x : A) : word v [72, 37, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_732 v H)
lemma reduced_733 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_733 v H)
lemma mul_reduced_733 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_733 v H)
lemma reduced_734 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_734 v H)
lemma mul_reduced_734 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_734 v H)
lemma reduced_735 : word v [21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_735 v H)
lemma mul_reduced_735 (x : A) : word v [21, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_735 v H)
lemma reduced_736 : word v [36, 70, 22, 3, 40, 60, 4, 54, 16, 58]=word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_736 v H)
lemma mul_reduced_736 (x : A) : word v [36, 70, 22, 3, 40, 60, 4, 54, 16, 58]*x=(word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_736 v H)
lemma reduced_737 : word v [49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_737 v H)
lemma mul_reduced_737 (x : A) : word v [49, 69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_737 v H)
lemma reduced_738 : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_738 v H)
lemma mul_reduced_738 (x : A) : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_738 v H)
lemma reduced_739 : word v [36, 70, 22, 3, 40, 60, 4, 54, 16, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_739 v H)
lemma mul_reduced_739 (x : A) : word v [36, 70, 22, 3, 40, 60, 4, 54, 16, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_739 v H)
lemma reduced_740 : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_740 v H)
lemma mul_reduced_740 (x : A) : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_740 v H)
lemma reduced_741 : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_741 v H)
lemma mul_reduced_741 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_741 v H)
lemma reduced_742 : word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 52]=word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_742 v H)
lemma mul_reduced_742 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 52]*x=(word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_742 v H)
lemma reduced_743 : word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_743 v H)
lemma mul_reduced_743 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 52]*x=(word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_743 v H)
lemma reduced_744 : word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_744 v H)
lemma mul_reduced_744 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 52]*x=(word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_744 v H)
lemma reduced_745 : word v [24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_745 v H)
lemma mul_reduced_745 (x : A) : word v [24, 18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_745 v H)
lemma reduced_746 : word v [28, 14, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_746 v H)
lemma mul_reduced_746 (x : A) : word v [28, 14, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_746 v H)
lemma reduced_747 : word v [40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_747 v H)
lemma mul_reduced_747 (x : A) : word v [40, 60, 4, 54, 15, 1, 34, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_747 v H)
lemma reduced_748 : word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_748 v H)
lemma mul_reduced_748 (x : A) : word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_748 v H)
lemma reduced_749 : word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_749 v H)
lemma mul_reduced_749 (x : A) : word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_749 v H)
lemma reduced_750 : word v [35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_750 v H)
lemma mul_reduced_750 (x : A) : word v [35, 55, 27, 58, 34, 63, 21, 70, 22, 3]*x=(-(word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_750 v H)
lemma reduced_751 : word v [52, 41, 43, 47, 7, 17, 21, 70, 22, 3]=word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 68] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_751 v H)
lemma mul_reduced_751 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 70, 22, 3]*x=(word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 68]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_751 v H)
lemma reduced_752 : word v [27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_752 v H)
lemma mul_reduced_752 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_752 v H)
lemma reduced_753 : word v [43, 47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_753 v H)
lemma mul_reduced_753 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_753 v H)
lemma reduced_754 : word v [45, 6, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_754 v H)
lemma mul_reduced_754 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_754 v H)
lemma reduced_755 : word v [27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_755 v H)
lemma mul_reduced_755 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 66, 25, 62]*x=(word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_755 v H)
lemma reduced_756 : word v [43, 47, 7, 17, 21, 69, 8, 66, 25, 62]=word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_756 v H)
lemma mul_reduced_756 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 66, 25, 62]*x=(word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_756 v H)
lemma reduced_757 : word v [45, 6, 7, 17, 21, 69, 8, 66, 25, 62]=word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_757 v H)
lemma mul_reduced_757 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 66, 25, 62]*x=(word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_757 v H)
lemma reduced_758 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_758 v H)
lemma mul_reduced_758 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_758 v H)
lemma reduced_759 : word v [27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_759 v H)
lemma mul_reduced_759 (x : A) : word v [27, 58, 33, 13, 49, 71, 72, 38, 28, 14]*x=(word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_759 v H)
lemma reduced_760 : word v [43, 48, 51, 64, 36, 71, 72, 38, 28, 14]=(-word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_760 v H)
lemma mul_reduced_760 (x : A) : word v [43, 48, 51, 64, 36, 71, 72, 38, 28, 14]*x=(-(word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_760 v H)
lemma reduced_761 : word v [46, 48, 51, 64, 36, 71, 72, 38, 28, 14]=(-word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_761 v H)
lemma mul_reduced_761 (x : A) : word v [46, 48, 51, 64, 36, 71, 72, 38, 28, 14]*x=(-(word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_761 v H)
lemma reduced_762 : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_762 v H)
lemma mul_reduced_762 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 65]*x=(word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_762 v H)
lemma reduced_763 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_763 v H)
lemma mul_reduced_763 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 54]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_763 v H)
lemma reduced_764 : word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_764 v H)
lemma mul_reduced_764 (x : A) : word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 69]*x=(-(word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_764 v H)
lemma reduced_765 : word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 69]=(-word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_765 v H)
lemma mul_reduced_765 (x : A) : word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 69]*x=(-(word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_765 v H)
lemma reduced_766 : word v [41, 43, 48, 51, 64, 36, 71, 72, 38, 29]=(-word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_766 v H)
lemma mul_reduced_766 (x : A) : word v [41, 43, 48, 51, 64, 36, 71, 72, 38, 29]*x=(-(word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_766 v H)
lemma reduced_767 : word v [55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_767 v H)
lemma mul_reduced_767 (x : A) : word v [55, 27, 58, 33, 13, 49, 71, 72, 38, 29]*x=(word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_767 v H)
lemma reduced_768 : word v [11, 26, 31, 73, 67, 32, 62, 52, 42, 46]=word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 43] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_768 v H)
lemma mul_reduced_768 (x : A) : word v [11, 26, 31, 73, 67, 32, 62, 52, 42, 46]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 43]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_768 v H)
lemma reduced_769 : word v [26, 31, 73, 67, 32, 61, 35, 56, 43, 48]=word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_769 v H)
lemma mul_reduced_769 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 56, 43, 48]*x=(word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_769 v H)
lemma reduced_770 : word v [26, 31, 73, 67, 32, 62, 52, 42, 45, 6]=word v [26, 31, 73, 67, 32, 61, 35, 56, 43, 47] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_770 v H)
lemma mul_reduced_770 (x : A) : word v [26, 31, 73, 67, 32, 62, 52, 42, 45, 6]*x=(word v [26, 31, 73, 67, 32, 61, 35, 56, 43, 47]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_770 v H)
lemma reduced_771 : word v [31, 73, 67, 32, 61, 35, 56, 43, 47, 7]=word v [31, 73, 67, 32, 61, 35, 55, 27, 59, 50] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_771 v H)
lemma mul_reduced_771 (x : A) : word v [31, 73, 67, 32, 61, 35, 56, 43, 47, 7]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 59, 50]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_771 v H)
lemma reduced_772 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_772 v H)
lemma mul_reduced_772 (x : A) : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_772 v H)
lemma reduced_773 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_773 v H)
lemma mul_reduced_773 (x : A) : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_773 v H)
lemma reduced_774 : word v [73, 67, 32, 61, 35, 55, 27, 59, 50, 17]=word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_774 v H)
lemma mul_reduced_774 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 59, 50, 17]*x=(word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_774 v H)
lemma reduced_775 : word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_775 v H)
lemma mul_reduced_775 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 56]*x=(word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_775 v H)
lemma reduced_776 : word v [10, 11, 26, 31, 73, 67, 32, 62, 52, 41]=word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_776 v H)
lemma mul_reduced_776 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 62, 52, 41]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_776 v H)
lemma reduced_777 : word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_777 v H)
lemma mul_reduced_777 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 56]*x=(word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_777 v H)
lemma reduced_778 : word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_778 v H)
lemma mul_reduced_778 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 56]*x=(word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_778 v H)
lemma reduced_779 : word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 44]=word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_779 v H)
lemma mul_reduced_779 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 44]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_779 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_720 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_720 (a k) (relation_zero k)
lemma reduced_721 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_721 (a k) (relation_zero k)
lemma reduced_722 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_722 (a k) (relation_zero k)
lemma reduced_723 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_723 (a k) (relation_zero k)
lemma reduced_724 : word (a k) [7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_724 (a k) (relation_zero k)
lemma reduced_725 : word (a k) [33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_725 (a k) (relation_zero k)
lemma reduced_726 : word (a k) [50, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_726 (a k) (relation_zero k)
lemma reduced_727 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_727 (a k) (relation_zero k)
lemma reduced_728 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_728 (a k) (relation_zero k)
lemma reduced_729 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_729 (a k) (relation_zero k)
lemma reduced_730 : word (a k) [8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_730 (a k) (relation_zero k)
lemma reduced_731 : word (a k) [22, 3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.reduced_731 (a k) (relation_zero k)
lemma reduced_732 : word (a k) [72, 37, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_732 (a k) (relation_zero k)
lemma reduced_733 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_733 (a k) (relation_zero k)
lemma reduced_734 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.reduced_734 (a k) (relation_zero k)
lemma reduced_735 : word (a k) [21, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_735 (a k) (relation_zero k)
lemma reduced_736 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 16, 58]=word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1] := by
  exact Universal.reduced_736 (a k) (relation_zero k)
lemma reduced_737 : word (a k) [49, 69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_737 (a k) (relation_zero k)
lemma reduced_738 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_738 (a k) (relation_zero k)
lemma reduced_739 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 16, 59]=0 := by
  exact Universal.reduced_739 (a k) (relation_zero k)
lemma reduced_740 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_740 (a k) (relation_zero k)
lemma reduced_741 : word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_741 (a k) (relation_zero k)
lemma reduced_742 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19, 52]=word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_742 (a k) (relation_zero k)
lemma reduced_743 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_743 (a k) (relation_zero k)
lemma reduced_744 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_744 (a k) (relation_zero k)
lemma reduced_745 : word (a k) [24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_745 (a k) (relation_zero k)
lemma reduced_746 : word (a k) [28, 14, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_746 (a k) (relation_zero k)
lemma reduced_747 : word (a k) [40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.reduced_747 (a k) (relation_zero k)
lemma reduced_748 : word (a k) [32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_748 (a k) (relation_zero k)
lemma reduced_749 : word (a k) [39, 12, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_749 (a k) (relation_zero k)
lemma reduced_750 : word (a k) [35, 55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_750 (a k) (relation_zero k)
lemma reduced_751 : word (a k) [52, 41, 43, 47, 7, 17, 21, 70, 22, 3]=word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 68] := by
  exact Universal.reduced_751 (a k) (relation_zero k)
lemma reduced_752 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_752 (a k) (relation_zero k)
lemma reduced_753 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_753 (a k) (relation_zero k)
lemma reduced_754 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_754 (a k) (relation_zero k)
lemma reduced_755 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_755 (a k) (relation_zero k)
lemma reduced_756 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 25, 62]=word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_756 (a k) (relation_zero k)
lemma reduced_757 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 25, 62]=word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_757 (a k) (relation_zero k)
lemma reduced_758 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.reduced_758 (a k) (relation_zero k)
lemma reduced_759 : word (a k) [27, 58, 33, 13, 49, 71, 72, 38, 28, 14]=word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_759 (a k) (relation_zero k)
lemma reduced_760 : word (a k) [43, 48, 51, 64, 36, 71, 72, 38, 28, 14]=(-word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18]) := by
  exact Universal.reduced_760 (a k) (relation_zero k)
lemma reduced_761 : word (a k) [46, 48, 51, 64, 36, 71, 72, 38, 28, 14]=(-word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18]) := by
  exact Universal.reduced_761 (a k) (relation_zero k)
lemma reduced_762 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  exact Universal.reduced_762 (a k) (relation_zero k)
lemma reduced_763 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  exact Universal.reduced_763 (a k) (relation_zero k)
lemma reduced_764 : word (a k) [32, 61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_764 (a k) (relation_zero k)
lemma reduced_765 : word (a k) [39, 12, 35, 55, 27, 58, 34, 63, 21, 69]=(-word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_765 (a k) (relation_zero k)
lemma reduced_766 : word (a k) [41, 43, 48, 51, 64, 36, 71, 72, 38, 29]=(-word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24]) := by
  exact Universal.reduced_766 (a k) (relation_zero k)
lemma reduced_767 : word (a k) [55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_767 (a k) (relation_zero k)
lemma reduced_768 : word (a k) [11, 26, 31, 73, 67, 32, 62, 52, 42, 46]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 56, 43] := by
  exact Universal.reduced_768 (a k) (relation_zero k)
lemma reduced_769 : word (a k) [26, 31, 73, 67, 32, 61, 35, 56, 43, 48]=word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 59] := by
  exact Universal.reduced_769 (a k) (relation_zero k)
lemma reduced_770 : word (a k) [26, 31, 73, 67, 32, 62, 52, 42, 45, 6]=word (a k) [26, 31, 73, 67, 32, 61, 35, 56, 43, 47] := by
  exact Universal.reduced_770 (a k) (relation_zero k)
lemma reduced_771 : word (a k) [31, 73, 67, 32, 61, 35, 56, 43, 47, 7]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 59, 50] := by
  exact Universal.reduced_771 (a k) (relation_zero k)
lemma reduced_772 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_772 (a k) (relation_zero k)
lemma reduced_773 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_773 (a k) (relation_zero k)
lemma reduced_774 : word (a k) [73, 67, 32, 61, 35, 55, 27, 59, 50, 17]=word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  exact Universal.reduced_774 (a k) (relation_zero k)
lemma reduced_775 : word (a k) [7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_775 (a k) (relation_zero k)
lemma reduced_776 : word (a k) [10, 11, 26, 31, 73, 67, 32, 62, 52, 41]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 56] := by
  exact Universal.reduced_776 (a k) (relation_zero k)
lemma reduced_777 : word (a k) [33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_777 (a k) (relation_zero k)
lemma reduced_778 : word (a k) [50, 17, 21, 69, 8, 66, 24, 19, 53, 56]=word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_778 (a k) (relation_zero k)
lemma reduced_779 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 56, 44]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27] := by
  exact Universal.reduced_779 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
