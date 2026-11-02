import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_660 : word v [47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_660 v H)
lemma mul_reduced_660 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_660 v H)
lemma reduced_661 : word v [58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_661 v H)
lemma mul_reduced_661 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_661 v H)
lemma reduced_662 : word v [6, 7, 17, 21, 69, 8, 66, 25, 62]=word v [6, 7, 17, 21, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_662 v H)
lemma mul_reduced_662 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 25, 62]*x=(word v [6, 7, 17, 21, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_662 v H)
lemma reduced_663 : word v [47, 7, 17, 21, 69, 8, 66, 25, 62]=word v [47, 7, 17, 21, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_663 v H)
lemma mul_reduced_663 (x : A) : word v [47, 7, 17, 21, 69, 8, 66, 25, 62]*x=(word v [47, 7, 17, 21, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_663 v H)
lemma reduced_664 : word v [58, 33, 13, 49, 69, 8, 66, 25, 62]=word v [58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_664 v H)
lemma mul_reduced_664 (x : A) : word v [58, 33, 13, 49, 69, 8, 66, 25, 62]*x=(word v [58, 33, 13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_664 v H)
lemma reduced_665 : word v [31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_665 v H)
lemma mul_reduced_665 (x : A) : word v [31, 73, 67, 32, 61, 35, 55, 27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_665 v H)
lemma reduced_666 : word v [48, 51, 64, 36, 71, 72, 38, 28, 14]=(-word v [47, 7, 17, 21, 69, 8, 66, 24, 18]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_666 v H)
lemma mul_reduced_666 (x : A) : word v [48, 51, 64, 36, 71, 72, 38, 28, 14]*x=(-(word v [47, 7, 17, 21, 69, 8, 66, 24, 18]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_666 v H)
lemma reduced_667 : word v [58, 33, 13, 49, 71, 72, 38, 28, 14]=word v [58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_667 v H)
lemma mul_reduced_667 (x : A) : word v [58, 33, 13, 49, 71, 72, 38, 28, 14]*x=(word v [58, 33, 13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_667 v H)
lemma reduced_668 : word v [74, 10, 11, 26, 31, 73, 67, 32, 60]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_668 v H)
lemma mul_reduced_668 (x : A) : word v [74, 10, 11, 26, 31, 73, 67, 32, 60]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_668 v H)
lemma reduced_669 : word v [67, 32, 61, 35, 55, 27, 58, 34, 65]=word v [67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_669 v H)
lemma mul_reduced_669 (x : A) : word v [67, 32, 61, 35, 55, 27, 58, 34, 65]*x=(word v [67, 32, 61, 35, 55, 27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_669 v H)
lemma reduced_670 : word v [11, 26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_670 v H)
lemma mul_reduced_670 (x : A) : word v [11, 26, 31, 73, 67, 32, 61, 35, 54]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_670 v H)
lemma reduced_671 : word v [12, 35, 55, 27, 58, 34, 63, 21, 69]=(-word v [12, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_671 v H)
lemma mul_reduced_671 (x : A) : word v [12, 35, 55, 27, 58, 34, 63, 21, 69]*x=(-(word v [12, 35, 55, 27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_671 v H)
lemma reduced_672 : word v [61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word v [61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_672 v H)
lemma mul_reduced_672 (x : A) : word v [61, 35, 55, 27, 58, 34, 63, 21, 69]*x=(-(word v [61, 35, 55, 27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_672 v H)
lemma reduced_673 : word v [27, 58, 33, 13, 49, 71, 72, 38, 29]=word v [27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_673 v H)
lemma mul_reduced_673 (x : A) : word v [27, 58, 33, 13, 49, 71, 72, 38, 29]*x=(word v [27, 58, 33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_673 v H)
lemma reduced_674 : word v [43, 48, 51, 64, 36, 71, 72, 38, 29]=(-word v [43, 47, 7, 17, 21, 69, 8, 66, 24]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_674 v H)
lemma mul_reduced_674 (x : A) : word v [43, 48, 51, 64, 36, 71, 72, 38, 29]*x=(-(word v [43, 47, 7, 17, 21, 69, 8, 66, 24]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_674 v H)
lemma reduced_675 : word v [46, 48, 51, 64, 36, 71, 72, 38, 29]=(-word v [45, 6, 7, 17, 21, 69, 8, 66, 24]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_675 v H)
lemma mul_reduced_675 (x : A) : word v [46, 48, 51, 64, 36, 71, 72, 38, 29]*x=(-(word v [45, 6, 7, 17, 21, 69, 8, 66, 24]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_675 v H)
lemma reduced_676 : word v [74, 10, 11, 26, 31, 73, 68, 39, 12]=word v [74, 10, 11, 26, 31, 73, 67, 32, 61] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_676 v H)
lemma mul_reduced_676 (x : A) : word v [74, 10, 11, 26, 31, 73, 68, 39, 12]*x=(word v [74, 10, 11, 26, 31, 73, 67, 32, 61]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_676 v H)
lemma reduced_677 : word v [26, 31, 73, 67, 32, 62, 52, 42, 46]=word v [26, 31, 73, 67, 32, 61, 35, 56, 43] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_677 v H)
lemma mul_reduced_677 (x : A) : word v [26, 31, 73, 67, 32, 62, 52, 42, 46]*x=(word v [26, 31, 73, 67, 32, 61, 35, 56, 43]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_677 v H)
lemma reduced_678 : word v [31, 73, 67, 32, 61, 35, 56, 43, 48]=word v [31, 73, 67, 32, 61, 35, 55, 27, 59] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_678 v H)
lemma mul_reduced_678 (x : A) : word v [31, 73, 67, 32, 61, 35, 56, 43, 48]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27, 59]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_678 v H)
lemma reduced_679 : word v [31, 73, 67, 32, 62, 52, 42, 45, 6]=word v [31, 73, 67, 32, 61, 35, 56, 43, 47] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_679 v H)
lemma mul_reduced_679 (x : A) : word v [31, 73, 67, 32, 62, 52, 42, 45, 6]*x=(word v [31, 73, 67, 32, 61, 35, 56, 43, 47]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_679 v H)
lemma reduced_680 : word v [73, 67, 32, 61, 35, 56, 43, 47, 7]=word v [73, 67, 32, 61, 35, 55, 27, 59, 50] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_680 v H)
lemma mul_reduced_680 (x : A) : word v [73, 67, 32, 61, 35, 56, 43, 47, 7]*x=(word v [73, 67, 32, 61, 35, 55, 27, 59, 50]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_680 v H)
lemma reduced_681 : word v [12, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_681 v H)
lemma mul_reduced_681 (x : A) : word v [12, 35, 55, 27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_681 v H)
lemma reduced_682 : word v [61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_682 v H)
lemma mul_reduced_682 (x : A) : word v [61, 35, 55, 27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_682 v H)
lemma reduced_683 : word v [67, 32, 61, 35, 55, 27, 59, 50, 17]=word v [67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_683 v H)
lemma mul_reduced_683 (x : A) : word v [67, 32, 61, 35, 55, 27, 59, 50, 17]*x=(word v [67, 32, 61, 35, 55, 27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_683 v H)
lemma reduced_684 : word v [11, 26, 31, 73, 67, 32, 62, 52, 41]=word v [11, 26, 31, 73, 67, 32, 61, 35, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_684 v H)
lemma mul_reduced_684 (x : A) : word v [11, 26, 31, 73, 67, 32, 62, 52, 41]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_684 v H)
lemma reduced_685 : word v [13, 49, 69, 8, 66, 24, 19, 53, 56]=word v [13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_685 v H)
lemma mul_reduced_685 (x : A) : word v [13, 49, 69, 8, 66, 24, 19, 53, 56]*x=(word v [13, 49, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_685 v H)
lemma reduced_686 : word v [17, 21, 69, 8, 66, 24, 19, 53, 56]=word v [17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_686 v H)
lemma mul_reduced_686 (x : A) : word v [17, 21, 69, 8, 66, 24, 19, 53, 56]*x=(word v [17, 21, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_686 v H)
lemma reduced_687 : word v [63, 21, 69, 8, 66, 24, 19, 53, 56]=word v [63, 21, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_687 v H)
lemma mul_reduced_687 (x : A) : word v [63, 21, 69, 8, 66, 24, 19, 53, 56]*x=(word v [63, 21, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_687 v H)
lemma reduced_688 : word v [21, 69, 8, 66, 24, 19, 53, 54, 16]=word v [21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_688 v H)
lemma mul_reduced_688 (x : A) : word v [21, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [21, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_688 v H)
lemma reduced_689 : word v [26, 31, 73, 67, 32, 61, 35, 56, 44]=word v [26, 31, 73, 67, 32, 61, 35, 55, 27] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_689 v H)
lemma mul_reduced_689 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 56, 44]*x=(word v [26, 31, 73, 67, 32, 61, 35, 55, 27]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_689 v H)
lemma reduced_690 : word v [36, 70, 22, 3, 40, 60, 4, 56, 44]=word v [36, 70, 22, 3, 40, 60, 4, 54, 16] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_690 v H)
lemma mul_reduced_690 (x : A) : word v [36, 70, 22, 3, 40, 60, 4, 56, 44]*x=(word v [36, 70, 22, 3, 40, 60, 4, 54, 16]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_690 v H)
lemma reduced_691 : word v [49, 69, 8, 66, 24, 19, 53, 54, 16]=word v [49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_691 v H)
lemma mul_reduced_691 (x : A) : word v [49, 69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [49, 69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_691 v H)
lemma reduced_692 : word v [8, 66, 24, 18, 9, 41, 44, 58, 34]=word v [8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_692 v H)
lemma mul_reduced_692 (x : A) : word v [8, 66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [8, 66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_692 v H)
lemma reduced_693 : word v [22, 3, 40, 60, 4, 54, 16, 57, 5]=word v [22, 3, 40, 60, 4, 54, 15, 1, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_693 v H)
lemma mul_reduced_693 (x : A) : word v [22, 3, 40, 60, 4, 54, 16, 57, 5]*x=(word v [22, 3, 40, 60, 4, 54, 15, 1, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_693 v H)
lemma reduced_694 : word v [72, 37, 24, 18, 9, 41, 44, 58, 34]=word v [72, 37, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_694 v H)
lemma mul_reduced_694 (x : A) : word v [72, 37, 24, 18, 9, 41, 44, 58, 34]*x=(word v [72, 37, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_694 v H)
lemma reduced_695 : word v [73, 67, 32, 61, 35, 55, 27, 59, 51]=word v [73, 67, 32, 61, 35, 55, 27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_695 v H)
lemma mul_reduced_695 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 59, 51]*x=(word v [73, 67, 32, 61, 35, 55, 27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_695 v H)
lemma reduced_696 : word v [7, 17, 21, 69, 8, 66, 25, 60, 4]=word v [7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_696 v H)
lemma mul_reduced_696 (x : A) : word v [7, 17, 21, 69, 8, 66, 25, 60, 4]*x=(word v [7, 17, 21, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_696 v H)
lemma reduced_697 : word v [10, 11, 26, 31, 73, 67, 32, 62, 53]=word v [10, 11, 26, 31, 73, 67, 32, 61, 35] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_697 v H)
lemma mul_reduced_697 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 62, 53]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61, 35]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_697 v H)
lemma reduced_698 : word v [33, 13, 49, 69, 8, 66, 25, 60, 4]=word v [33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_698 v H)
lemma mul_reduced_698 (x : A) : word v [33, 13, 49, 69, 8, 66, 25, 60, 4]*x=(word v [33, 13, 49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_698 v H)
lemma reduced_699 : word v [50, 17, 21, 69, 8, 66, 25, 60, 4]=word v [50, 17, 21, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_699 v H)
lemma mul_reduced_699 (x : A) : word v [50, 17, 21, 69, 8, 66, 25, 60, 4]*x=(word v [50, 17, 21, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_699 v H)
lemma reduced_700 : word v [24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_700 v H)
lemma mul_reduced_700 (x : A) : word v [24, 18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_700 v H)
lemma reduced_701 : word v [28, 14, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_701 v H)
lemma mul_reduced_701 (x : A) : word v [28, 14, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_701 v H)
lemma reduced_702 : word v [32, 61, 35, 55, 27, 58, 34, 64, 36]=word v [32, 61, 35, 55, 27, 58, 34, 63, 21] + word v [32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_702 v H)
lemma mul_reduced_702 (x : A) : word v [32, 61, 35, 55, 27, 58, 34, 64, 36]*x=(word v [32, 61, 35, 55, 27, 58, 34, 63, 21]*x) + (word v [32, 61, 35, 55, 27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_702 v H)
lemma reduced_703 : word v [39, 12, 35, 55, 27, 58, 34, 64, 36]=word v [39, 12, 35, 55, 27, 58, 34, 63, 21] + word v [39, 12, 35, 55, 27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_703 v H)
lemma mul_reduced_703 (x : A) : word v [39, 12, 35, 55, 27, 58, 34, 64, 36]*x=(word v [39, 12, 35, 55, 27, 58, 34, 63, 21]*x) + (word v [39, 12, 35, 55, 27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_703 v H)
lemma reduced_704 : word v [40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_704 v H)
lemma mul_reduced_704 (x : A) : word v [40, 60, 4, 54, 15, 1, 34, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_704 v H)
lemma reduced_705 : word v [27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word v [27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_705 v H)
lemma mul_reduced_705 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 68, 40]*x=(-(word v [27, 58, 33, 13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_705 v H)
lemma reduced_706 : word v [43, 47, 7, 17, 21, 69, 8, 68, 40]=(-word v [43, 47, 7, 17, 21, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_706 v H)
lemma mul_reduced_706 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 68, 40]*x=(-(word v [43, 47, 7, 17, 21, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_706 v H)
lemma reduced_707 : word v [45, 6, 7, 17, 21, 69, 8, 68, 40]=(-word v [45, 6, 7, 17, 21, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_707 v H)
lemma mul_reduced_707 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 68, 40]*x=(-(word v [45, 6, 7, 17, 21, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_707 v H)
lemma reduced_708 : word v [35, 55, 27, 58, 33, 13, 49, 71, 73]=word v [35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_708 v H)
lemma mul_reduced_708 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 71, 73]*x=(word v [35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_708 v H)
lemma reduced_709 : word v [35, 55, 27, 58, 34, 63, 21, 70, 23]=word v [35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_709 v H)
lemma mul_reduced_709 (x : A) : word v [35, 55, 27, 58, 34, 63, 21, 70, 23]*x=(word v [35, 55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_709 v H)
lemma reduced_710 : word v [52, 41, 43, 47, 7, 17, 21, 70, 23]=(-word v [52, 41, 43, 47, 7, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_710 v H)
lemma mul_reduced_710 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 70, 23]*x=(-(word v [52, 41, 43, 47, 7, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_710 v H)
lemma reduced_711 : word v [52, 41, 43, 48, 51, 64, 36, 71, 73]=(-word v [52, 41, 43, 47, 7, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_711 v H)
lemma mul_reduced_711 (x : A) : word v [52, 41, 43, 48, 51, 64, 36, 71, 73]*x=(-(word v [52, 41, 43, 47, 7, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_711 v H)
lemma reduced_712 : word v [41, 43, 48, 51, 64, 36, 71, 72, 37]=(-word v [41, 43, 47, 7, 17, 21, 69, 8, 66]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_712 v H)
lemma mul_reduced_712 (x : A) : word v [41, 43, 48, 51, 64, 36, 71, 72, 37]*x=(-(word v [41, 43, 47, 7, 17, 21, 69, 8, 66]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_712 v H)
lemma reduced_713 : word v [55, 27, 58, 33, 13, 49, 71, 72, 37]=word v [55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_713 v H)
lemma mul_reduced_713 (x : A) : word v [55, 27, 58, 33, 13, 49, 71, 72, 37]*x=(word v [55, 27, 58, 33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_713 v H)
lemma reduced_714 : word v [69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_714 v H)
lemma mul_reduced_714 (x : A) : word v [69, 8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_714 v H)
lemma reduced_715 : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_715 v H)
lemma mul_reduced_715 (x : A) : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_715 v H)
lemma reduced_716 : word v [8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_716 v H)
lemma mul_reduced_716 (x : A) : word v [8, 66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_716 v H)
lemma reduced_717 : word v [22, 3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_717 v H)
lemma mul_reduced_717 (x : A) : word v [22, 3, 40, 60, 4, 54, 15, 1, 34, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_717 v H)
lemma reduced_718 : word v [72, 37, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_718 v H)
lemma mul_reduced_718 (x : A) : word v [72, 37, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_718 v H)
lemma reduced_719 : word v [41, 43, 47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_719 v H)
lemma mul_reduced_719 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_719 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_660 : word (a k) [47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_660 (a k) (relation_zero k)
lemma reduced_661 : word (a k) [58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_661 (a k) (relation_zero k)
lemma reduced_662 : word (a k) [6, 7, 17, 21, 69, 8, 66, 25, 62]=word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_662 (a k) (relation_zero k)
lemma reduced_663 : word (a k) [47, 7, 17, 21, 69, 8, 66, 25, 62]=word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_663 (a k) (relation_zero k)
lemma reduced_664 : word (a k) [58, 33, 13, 49, 69, 8, 66, 25, 62]=word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_664 (a k) (relation_zero k)
lemma reduced_665 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.reduced_665 (a k) (relation_zero k)
lemma reduced_666 : word (a k) [48, 51, 64, 36, 71, 72, 38, 28, 14]=(-word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18]) := by
  exact Universal.reduced_666 (a k) (relation_zero k)
lemma reduced_667 : word (a k) [58, 33, 13, 49, 71, 72, 38, 28, 14]=word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_667 (a k) (relation_zero k)
lemma reduced_668 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 60]=0 := by
  exact Universal.reduced_668 (a k) (relation_zero k)
lemma reduced_669 : word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 65]=word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13] := by
  exact Universal.reduced_669 (a k) (relation_zero k)
lemma reduced_670 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  exact Universal.reduced_670 (a k) (relation_zero k)
lemma reduced_671 : word (a k) [12, 35, 55, 27, 58, 34, 63, 21, 69]=(-word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_671 (a k) (relation_zero k)
lemma reduced_672 : word (a k) [61, 35, 55, 27, 58, 34, 63, 21, 69]=(-word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_672 (a k) (relation_zero k)
lemma reduced_673 : word (a k) [27, 58, 33, 13, 49, 71, 72, 38, 29]=word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_673 (a k) (relation_zero k)
lemma reduced_674 : word (a k) [43, 48, 51, 64, 36, 71, 72, 38, 29]=(-word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24]) := by
  exact Universal.reduced_674 (a k) (relation_zero k)
lemma reduced_675 : word (a k) [46, 48, 51, 64, 36, 71, 72, 38, 29]=(-word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24]) := by
  exact Universal.reduced_675 (a k) (relation_zero k)
lemma reduced_676 : word (a k) [74, 10, 11, 26, 31, 73, 68, 39, 12]=word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61] := by
  exact Universal.reduced_676 (a k) (relation_zero k)
lemma reduced_677 : word (a k) [26, 31, 73, 67, 32, 62, 52, 42, 46]=word (a k) [26, 31, 73, 67, 32, 61, 35, 56, 43] := by
  exact Universal.reduced_677 (a k) (relation_zero k)
lemma reduced_678 : word (a k) [31, 73, 67, 32, 61, 35, 56, 43, 48]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 59] := by
  exact Universal.reduced_678 (a k) (relation_zero k)
lemma reduced_679 : word (a k) [31, 73, 67, 32, 62, 52, 42, 45, 6]=word (a k) [31, 73, 67, 32, 61, 35, 56, 43, 47] := by
  exact Universal.reduced_679 (a k) (relation_zero k)
lemma reduced_680 : word (a k) [73, 67, 32, 61, 35, 56, 43, 47, 7]=word (a k) [73, 67, 32, 61, 35, 55, 27, 59, 50] := by
  exact Universal.reduced_680 (a k) (relation_zero k)
lemma reduced_681 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_681 (a k) (relation_zero k)
lemma reduced_682 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_682 (a k) (relation_zero k)
lemma reduced_683 : word (a k) [67, 32, 61, 35, 55, 27, 59, 50, 17]=word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63] := by
  exact Universal.reduced_683 (a k) (relation_zero k)
lemma reduced_684 : word (a k) [11, 26, 31, 73, 67, 32, 62, 52, 41]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 56] := by
  exact Universal.reduced_684 (a k) (relation_zero k)
lemma reduced_685 : word (a k) [13, 49, 69, 8, 66, 24, 19, 53, 56]=word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_685 (a k) (relation_zero k)
lemma reduced_686 : word (a k) [17, 21, 69, 8, 66, 24, 19, 53, 56]=word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_686 (a k) (relation_zero k)
lemma reduced_687 : word (a k) [63, 21, 69, 8, 66, 24, 19, 53, 56]=word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_687 (a k) (relation_zero k)
lemma reduced_688 : word (a k) [21, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_688 (a k) (relation_zero k)
lemma reduced_689 : word (a k) [26, 31, 73, 67, 32, 61, 35, 56, 44]=word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27] := by
  exact Universal.reduced_689 (a k) (relation_zero k)
lemma reduced_690 : word (a k) [36, 70, 22, 3, 40, 60, 4, 56, 44]=word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 16] := by
  exact Universal.reduced_690 (a k) (relation_zero k)
lemma reduced_691 : word (a k) [49, 69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_691 (a k) (relation_zero k)
lemma reduced_692 : word (a k) [8, 66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [8, 66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_692 (a k) (relation_zero k)
lemma reduced_693 : word (a k) [22, 3, 40, 60, 4, 54, 16, 57, 5]=word (a k) [22, 3, 40, 60, 4, 54, 15, 1, 34] := by
  exact Universal.reduced_693 (a k) (relation_zero k)
lemma reduced_694 : word (a k) [72, 37, 24, 18, 9, 41, 44, 58, 34]=word (a k) [72, 37, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_694 (a k) (relation_zero k)
lemma reduced_695 : word (a k) [73, 67, 32, 61, 35, 55, 27, 59, 51]=word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34] := by
  exact Universal.reduced_695 (a k) (relation_zero k)
lemma reduced_696 : word (a k) [7, 17, 21, 69, 8, 66, 25, 60, 4]=word (a k) [7, 17, 21, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_696 (a k) (relation_zero k)
lemma reduced_697 : word (a k) [10, 11, 26, 31, 73, 67, 32, 62, 53]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35] := by
  exact Universal.reduced_697 (a k) (relation_zero k)
lemma reduced_698 : word (a k) [33, 13, 49, 69, 8, 66, 25, 60, 4]=word (a k) [33, 13, 49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_698 (a k) (relation_zero k)
lemma reduced_699 : word (a k) [50, 17, 21, 69, 8, 66, 25, 60, 4]=word (a k) [50, 17, 21, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_699 (a k) (relation_zero k)
lemma reduced_700 : word (a k) [24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_700 (a k) (relation_zero k)
lemma reduced_701 : word (a k) [28, 14, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_701 (a k) (relation_zero k)
lemma reduced_702 : word (a k) [32, 61, 35, 55, 27, 58, 34, 64, 36]=word (a k) [32, 61, 35, 55, 27, 58, 34, 63, 21] + word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49] := by
  exact Universal.reduced_702 (a k) (relation_zero k)
lemma reduced_703 : word (a k) [39, 12, 35, 55, 27, 58, 34, 64, 36]=word (a k) [39, 12, 35, 55, 27, 58, 34, 63, 21] + word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49] := by
  exact Universal.reduced_703 (a k) (relation_zero k)
lemma reduced_704 : word (a k) [40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.reduced_704 (a k) (relation_zero k)
lemma reduced_705 : word (a k) [27, 58, 33, 13, 49, 69, 8, 68, 40]=(-word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_705 (a k) (relation_zero k)
lemma reduced_706 : word (a k) [43, 47, 7, 17, 21, 69, 8, 68, 40]=(-word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 25]) := by
  exact Universal.reduced_706 (a k) (relation_zero k)
lemma reduced_707 : word (a k) [45, 6, 7, 17, 21, 69, 8, 68, 40]=(-word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 25]) := by
  exact Universal.reduced_707 (a k) (relation_zero k)
lemma reduced_708 : word (a k) [35, 55, 27, 58, 33, 13, 49, 71, 73]=word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_708 (a k) (relation_zero k)
lemma reduced_709 : word (a k) [35, 55, 27, 58, 34, 63, 21, 70, 23]=word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_709 (a k) (relation_zero k)
lemma reduced_710 : word (a k) [52, 41, 43, 47, 7, 17, 21, 70, 23]=(-word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8]) := by
  exact Universal.reduced_710 (a k) (relation_zero k)
lemma reduced_711 : word (a k) [52, 41, 43, 48, 51, 64, 36, 71, 73]=(-word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8]) := by
  exact Universal.reduced_711 (a k) (relation_zero k)
lemma reduced_712 : word (a k) [41, 43, 48, 51, 64, 36, 71, 72, 37]=(-word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66]) := by
  exact Universal.reduced_712 (a k) (relation_zero k)
lemma reduced_713 : word (a k) [55, 27, 58, 33, 13, 49, 71, 72, 37]=word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_713 (a k) (relation_zero k)
lemma reduced_714 : word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_714 (a k) (relation_zero k)
lemma reduced_715 : word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  exact Universal.reduced_715 (a k) (relation_zero k)
lemma reduced_716 : word (a k) [8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_716 (a k) (relation_zero k)
lemma reduced_717 : word (a k) [22, 3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.reduced_717 (a k) (relation_zero k)
lemma reduced_718 : word (a k) [72, 37, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_718 (a k) (relation_zero k)
lemma reduced_719 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_719 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
