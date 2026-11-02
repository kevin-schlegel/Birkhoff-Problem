import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_600 : word v [11, 26, 31, 73, 67, 32, 62, 53]=word v [11, 26, 31, 73, 67, 32, 61, 35] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_600 v H)
lemma mul_reduced_600 (x : A) : word v [11, 26, 31, 73, 67, 32, 62, 53]*x=(word v [11, 26, 31, 73, 67, 32, 61, 35]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_600 v H)
lemma reduced_601 : word v [13, 49, 69, 8, 66, 25, 60, 4]=word v [13, 49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_601 v H)
lemma mul_reduced_601 (x : A) : word v [13, 49, 69, 8, 66, 25, 60, 4]*x=(word v [13, 49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_601 v H)
lemma reduced_602 : word v [17, 21, 69, 8, 66, 25, 60, 4]=word v [17, 21, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_602 v H)
lemma mul_reduced_602 (x : A) : word v [17, 21, 69, 8, 66, 25, 60, 4]*x=(word v [17, 21, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_602 v H)
lemma reduced_603 : word v [63, 21, 69, 8, 66, 25, 60, 4]=word v [63, 21, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_603 v H)
lemma mul_reduced_603 (x : A) : word v [63, 21, 69, 8, 66, 25, 60, 4]*x=(word v [63, 21, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_603 v H)
lemma reduced_604 : word v [12, 35, 55, 27, 58, 34, 64, 36]=word v [12, 35, 55, 27, 58, 34, 63, 21] + word v [12, 35, 55, 27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_604 v H)
lemma mul_reduced_604 (x : A) : word v [12, 35, 55, 27, 58, 34, 64, 36]*x=(word v [12, 35, 55, 27, 58, 34, 63, 21]*x) + (word v [12, 35, 55, 27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_604 v H)
lemma reduced_605 : word v [14, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_605 v H)
lemma mul_reduced_605 (x : A) : word v [14, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_605 v H)
lemma reduced_606 : word v [18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_606 v H)
lemma mul_reduced_606 (x : A) : word v [18, 9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_606 v H)
lemma reduced_607 : word v [60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_607 v H)
lemma mul_reduced_607 (x : A) : word v [60, 4, 54, 15, 1, 34, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_607 v H)
lemma reduced_608 : word v [61, 35, 55, 27, 58, 34, 64, 36]=word v [61, 35, 55, 27, 58, 34, 63, 21] + word v [61, 35, 55, 27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_608 v H)
lemma mul_reduced_608 (x : A) : word v [61, 35, 55, 27, 58, 34, 64, 36]*x=(word v [61, 35, 55, 27, 58, 34, 63, 21]*x) + (word v [61, 35, 55, 27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_608 v H)
lemma reduced_609 : word v [6, 7, 17, 21, 69, 8, 68, 40]=(-word v [6, 7, 17, 21, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_609 v H)
lemma mul_reduced_609 (x : A) : word v [6, 7, 17, 21, 69, 8, 68, 40]*x=(-(word v [6, 7, 17, 21, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_609 v H)
lemma reduced_610 : word v [47, 7, 17, 21, 69, 8, 68, 40]=(-word v [47, 7, 17, 21, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_610 v H)
lemma mul_reduced_610 (x : A) : word v [47, 7, 17, 21, 69, 8, 68, 40]*x=(-(word v [47, 7, 17, 21, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_610 v H)
lemma reduced_611 : word v [58, 33, 13, 49, 69, 8, 68, 40]=(-word v [58, 33, 13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_611 v H)
lemma mul_reduced_611 (x : A) : word v [58, 33, 13, 49, 69, 8, 68, 40]*x=(-(word v [58, 33, 13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_611 v H)
lemma reduced_612 : word v [74, 10, 11, 26, 31, 73, 68, 40]=word v [74, 10, 11, 26, 31, 73, 67, 32] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_612 v H)
lemma mul_reduced_612 (x : A) : word v [74, 10, 11, 26, 31, 73, 68, 40]*x=(word v [74, 10, 11, 26, 31, 73, 67, 32]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_612 v H)
lemma reduced_613 : word v [41, 43, 47, 7, 17, 21, 70, 23]=(-word v [41, 43, 47, 7, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_613 v H)
lemma mul_reduced_613 (x : A) : word v [41, 43, 47, 7, 17, 21, 70, 23]*x=(-(word v [41, 43, 47, 7, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_613 v H)
lemma reduced_614 : word v [41, 43, 48, 51, 64, 36, 71, 73]=(-word v [41, 43, 47, 7, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_614 v H)
lemma mul_reduced_614 (x : A) : word v [41, 43, 48, 51, 64, 36, 71, 73]*x=(-(word v [41, 43, 47, 7, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_614 v H)
lemma reduced_615 : word v [55, 27, 58, 33, 13, 49, 71, 73]=word v [55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_615 v H)
lemma mul_reduced_615 (x : A) : word v [55, 27, 58, 33, 13, 49, 71, 73]*x=(word v [55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_615 v H)
lemma reduced_616 : word v [55, 27, 58, 34, 63, 21, 70, 23]=word v [55, 27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_616 v H)
lemma mul_reduced_616 (x : A) : word v [55, 27, 58, 34, 63, 21, 70, 23]*x=(word v [55, 27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_616 v H)
lemma reduced_617 : word v [27, 58, 33, 13, 49, 71, 72, 37]=word v [27, 58, 33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_617 v H)
lemma mul_reduced_617 (x : A) : word v [27, 58, 33, 13, 49, 71, 72, 37]*x=(word v [27, 58, 33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_617 v H)
lemma reduced_618 : word v [43, 48, 51, 64, 36, 71, 72, 37]=(-word v [43, 47, 7, 17, 21, 69, 8, 66]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_618 v H)
lemma mul_reduced_618 (x : A) : word v [43, 48, 51, 64, 36, 71, 72, 37]*x=(-(word v [43, 47, 7, 17, 21, 69, 8, 66]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_618 v H)
lemma reduced_619 : word v [46, 48, 51, 64, 36, 71, 72, 37]=(-word v [45, 6, 7, 17, 21, 69, 8, 66]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_619 v H)
lemma mul_reduced_619 (x : A) : word v [46, 48, 51, 64, 36, 71, 72, 37]*x=(-(word v [45, 6, 7, 17, 21, 69, 8, 66]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_619 v H)
lemma reduced_620 : word v [8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_620 v H)
lemma mul_reduced_620 (x : A) : word v [8, 66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_620 v H)
lemma reduced_621 : word v [22, 3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_621 v H)
lemma mul_reduced_621 (x : A) : word v [22, 3, 40, 60, 4, 54, 15, 1, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_621 v H)
lemma reduced_622 : word v [72, 37, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_622 v H)
lemma mul_reduced_622 (x : A) : word v [72, 37, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_622 v H)
lemma reduced_623 : word v [3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_623 v H)
lemma mul_reduced_623 (x : A) : word v [3, 40, 60, 4, 54, 15, 1, 34, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_623 v H)
lemma reduced_624 : word v [37, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_624 v H)
lemma mul_reduced_624 (x : A) : word v [37, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_624 v H)
lemma reduced_625 : word v [66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_625 v H)
lemma mul_reduced_625 (x : A) : word v [66, 24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_625 v H)
lemma reduced_626 : word v [27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_626 v H)
lemma mul_reduced_626 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_626 v H)
lemma reduced_627 : word v [43, 47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_627 v H)
lemma mul_reduced_627 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_627 v H)
lemma reduced_628 : word v [45, 6, 7, 17, 21, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_628 v H)
lemma mul_reduced_628 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_628 v H)
lemma reduced_629 : word v [17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_629 v H)
lemma mul_reduced_629 (x : A) : word v [17, 21, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_629 v H)
lemma reduced_630 : word v [63, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_630 v H)
lemma mul_reduced_630 (x : A) : word v [63, 21, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_630 v H)
lemma reduced_631 : word v [13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_631 v H)
lemma mul_reduced_631 (x : A) : word v [13, 49, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_631 v H)
lemma reduced_632 : word v [17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_632 v H)
lemma mul_reduced_632 (x : A) : word v [17, 21, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_632 v H)
lemma reduced_633 : word v [63, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_633 v H)
lemma mul_reduced_633 (x : A) : word v [63, 21, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_633 v H)
lemma reduced_634 : word v [21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_634 v H)
lemma mul_reduced_634 (x : A) : word v [21, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_634 v H)
lemma reduced_635 : word v [36, 70, 22, 3, 40, 60, 4, 56, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_635 v H)
lemma mul_reduced_635 (x : A) : word v [36, 70, 22, 3, 40, 60, 4, 56, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_635 v H)
lemma reduced_636 : word v [49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_636 v H)
lemma mul_reduced_636 (x : A) : word v [49, 69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_636 v H)
lemma reduced_637 : word v [3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_637 v H)
lemma mul_reduced_637 (x : A) : word v [3, 40, 60, 4, 54, 15, 1, 34, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_637 v H)
lemma reduced_638 : word v [37, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_638 v H)
lemma mul_reduced_638 (x : A) : word v [37, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_638 v H)
lemma reduced_639 : word v [66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_639 v H)
lemma mul_reduced_639 (x : A) : word v [66, 24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_639 v H)
lemma reduced_640 : word v [41, 43, 47, 7, 17, 21, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_640 v H)
lemma mul_reduced_640 (x : A) : word v [41, 43, 47, 7, 17, 21, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_640 v H)
lemma reduced_641 : word v [55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_641 v H)
lemma mul_reduced_641 (x : A) : word v [55, 27, 58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_641 v H)
lemma reduced_642 : word v [13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_642 v H)
lemma mul_reduced_642 (x : A) : word v [13, 49, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_642 v H)
lemma reduced_643 : word v [69, 8, 66, 24, 19, 53, 54, 15, 1]=word v [69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_643 v H)
lemma mul_reduced_643 (x : A) : word v [69, 8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [69, 8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_643 v H)
lemma reduced_644 : word v [70, 22, 3, 40, 60, 4, 54, 16, 58]=word v [70, 22, 3, 40, 60, 4, 54, 15, 1] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_644 v H)
lemma mul_reduced_644 (x : A) : word v [70, 22, 3, 40, 60, 4, 54, 16, 58]*x=(word v [70, 22, 3, 40, 60, 4, 54, 15, 1]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_644 v H)
lemma reduced_645 : word v [69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_645 v H)
lemma mul_reduced_645 (x : A) : word v [69, 8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_645 v H)
lemma reduced_646 : word v [70, 22, 3, 40, 60, 4, 54, 16, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_646 v H)
lemma mul_reduced_646 (x : A) : word v [70, 22, 3, 40, 60, 4, 54, 16, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_646 v H)
lemma reduced_647 : word v [32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_647 v H)
lemma mul_reduced_647 (x : A) : word v [32, 61, 35, 55, 27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_647 v H)
lemma reduced_648 : word v [39, 12, 35, 55, 27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_648 v H)
lemma mul_reduced_648 (x : A) : word v [39, 12, 35, 55, 27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_648 v H)
lemma reduced_649 : word v [7, 17, 21, 69, 8, 66, 24, 19, 52]=word v [7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_649 v H)
lemma mul_reduced_649 (x : A) : word v [7, 17, 21, 69, 8, 66, 24, 19, 52]*x=(word v [7, 17, 21, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_649 v H)
lemma reduced_650 : word v [33, 13, 49, 69, 8, 66, 24, 19, 52]=word v [33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_650 v H)
lemma mul_reduced_650 (x : A) : word v [33, 13, 49, 69, 8, 66, 24, 19, 52]*x=(word v [33, 13, 49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_650 v H)
lemma reduced_651 : word v [50, 17, 21, 69, 8, 66, 24, 19, 52]=word v [50, 17, 21, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_651 v H)
lemma mul_reduced_651 (x : A) : word v [50, 17, 21, 69, 8, 66, 24, 19, 52]*x=(word v [50, 17, 21, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_651 v H)
lemma reduced_652 : word v [14, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_652 v H)
lemma mul_reduced_652 (x : A) : word v [14, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_652 v H)
lemma reduced_653 : word v [18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_653 v H)
lemma mul_reduced_653 (x : A) : word v [18, 9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_653 v H)
lemma reduced_654 : word v [60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_654 v H)
lemma mul_reduced_654 (x : A) : word v [60, 4, 54, 15, 1, 34, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_654 v H)
lemma reduced_655 : word v [12, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_655 v H)
lemma mul_reduced_655 (x : A) : word v [12, 35, 55, 27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_655 v H)
lemma reduced_656 : word v [61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_656 v H)
lemma mul_reduced_656 (x : A) : word v [61, 35, 55, 27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_656 v H)
lemma reduced_657 : word v [41, 43, 47, 7, 17, 21, 70, 22, 3]=word v [41, 43, 47, 7, 17, 21, 69, 8, 68] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_657 v H)
lemma mul_reduced_657 (x : A) : word v [41, 43, 47, 7, 17, 21, 70, 22, 3]*x=(word v [41, 43, 47, 7, 17, 21, 69, 8, 68]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_657 v H)
lemma reduced_658 : word v [55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word v [55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_658 v H)
lemma mul_reduced_658 (x : A) : word v [55, 27, 58, 34, 63, 21, 70, 22, 3]*x=(-(word v [55, 27, 58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_658 v H)
lemma reduced_659 : word v [6, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_659 v H)
lemma mul_reduced_659 (x : A) : word v [6, 7, 17, 21, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_659 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_600 : word (a k) [11, 26, 31, 73, 67, 32, 62, 53]=word (a k) [11, 26, 31, 73, 67, 32, 61, 35] := by
  exact Universal.reduced_600 (a k) (relation_zero k)
lemma reduced_601 : word (a k) [13, 49, 69, 8, 66, 25, 60, 4]=word (a k) [13, 49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_601 (a k) (relation_zero k)
lemma reduced_602 : word (a k) [17, 21, 69, 8, 66, 25, 60, 4]=word (a k) [17, 21, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_602 (a k) (relation_zero k)
lemma reduced_603 : word (a k) [63, 21, 69, 8, 66, 25, 60, 4]=word (a k) [63, 21, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_603 (a k) (relation_zero k)
lemma reduced_604 : word (a k) [12, 35, 55, 27, 58, 34, 64, 36]=word (a k) [12, 35, 55, 27, 58, 34, 63, 21] + word (a k) [12, 35, 55, 27, 58, 33, 13, 49] := by
  exact Universal.reduced_604 (a k) (relation_zero k)
lemma reduced_605 : word (a k) [14, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_605 (a k) (relation_zero k)
lemma reduced_606 : word (a k) [18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_606 (a k) (relation_zero k)
lemma reduced_607 : word (a k) [60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.reduced_607 (a k) (relation_zero k)
lemma reduced_608 : word (a k) [61, 35, 55, 27, 58, 34, 64, 36]=word (a k) [61, 35, 55, 27, 58, 34, 63, 21] + word (a k) [61, 35, 55, 27, 58, 33, 13, 49] := by
  exact Universal.reduced_608 (a k) (relation_zero k)
lemma reduced_609 : word (a k) [6, 7, 17, 21, 69, 8, 68, 40]=(-word (a k) [6, 7, 17, 21, 69, 8, 66, 25]) := by
  exact Universal.reduced_609 (a k) (relation_zero k)
lemma reduced_610 : word (a k) [47, 7, 17, 21, 69, 8, 68, 40]=(-word (a k) [47, 7, 17, 21, 69, 8, 66, 25]) := by
  exact Universal.reduced_610 (a k) (relation_zero k)
lemma reduced_611 : word (a k) [58, 33, 13, 49, 69, 8, 68, 40]=(-word (a k) [58, 33, 13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_611 (a k) (relation_zero k)
lemma reduced_612 : word (a k) [74, 10, 11, 26, 31, 73, 68, 40]=word (a k) [74, 10, 11, 26, 31, 73, 67, 32] := by
  exact Universal.reduced_612 (a k) (relation_zero k)
lemma reduced_613 : word (a k) [41, 43, 47, 7, 17, 21, 70, 23]=(-word (a k) [41, 43, 47, 7, 17, 21, 69, 8]) := by
  exact Universal.reduced_613 (a k) (relation_zero k)
lemma reduced_614 : word (a k) [41, 43, 48, 51, 64, 36, 71, 73]=(-word (a k) [41, 43, 47, 7, 17, 21, 69, 8]) := by
  exact Universal.reduced_614 (a k) (relation_zero k)
lemma reduced_615 : word (a k) [55, 27, 58, 33, 13, 49, 71, 73]=word (a k) [55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_615 (a k) (relation_zero k)
lemma reduced_616 : word (a k) [55, 27, 58, 34, 63, 21, 70, 23]=word (a k) [55, 27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_616 (a k) (relation_zero k)
lemma reduced_617 : word (a k) [27, 58, 33, 13, 49, 71, 72, 37]=word (a k) [27, 58, 33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_617 (a k) (relation_zero k)
lemma reduced_618 : word (a k) [43, 48, 51, 64, 36, 71, 72, 37]=(-word (a k) [43, 47, 7, 17, 21, 69, 8, 66]) := by
  exact Universal.reduced_618 (a k) (relation_zero k)
lemma reduced_619 : word (a k) [46, 48, 51, 64, 36, 71, 72, 37]=(-word (a k) [45, 6, 7, 17, 21, 69, 8, 66]) := by
  exact Universal.reduced_619 (a k) (relation_zero k)
lemma reduced_620 : word (a k) [8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_620 (a k) (relation_zero k)
lemma reduced_621 : word (a k) [22, 3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  exact Universal.reduced_621 (a k) (relation_zero k)
lemma reduced_622 : word (a k) [72, 37, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_622 (a k) (relation_zero k)
lemma reduced_623 : word (a k) [3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.reduced_623 (a k) (relation_zero k)
lemma reduced_624 : word (a k) [37, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_624 (a k) (relation_zero k)
lemma reduced_625 : word (a k) [66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_625 (a k) (relation_zero k)
lemma reduced_626 : word (a k) [27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_626 (a k) (relation_zero k)
lemma reduced_627 : word (a k) [43, 47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_627 (a k) (relation_zero k)
lemma reduced_628 : word (a k) [45, 6, 7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_628 (a k) (relation_zero k)
lemma reduced_629 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_629 (a k) (relation_zero k)
lemma reduced_630 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_630 (a k) (relation_zero k)
lemma reduced_631 : word (a k) [13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_631 (a k) (relation_zero k)
lemma reduced_632 : word (a k) [17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_632 (a k) (relation_zero k)
lemma reduced_633 : word (a k) [63, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_633 (a k) (relation_zero k)
lemma reduced_634 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_634 (a k) (relation_zero k)
lemma reduced_635 : word (a k) [36, 70, 22, 3, 40, 60, 4, 56, 43]=0 := by
  exact Universal.reduced_635 (a k) (relation_zero k)
lemma reduced_636 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_636 (a k) (relation_zero k)
lemma reduced_637 : word (a k) [3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.reduced_637 (a k) (relation_zero k)
lemma reduced_638 : word (a k) [37, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_638 (a k) (relation_zero k)
lemma reduced_639 : word (a k) [66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_639 (a k) (relation_zero k)
lemma reduced_640 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.reduced_640 (a k) (relation_zero k)
lemma reduced_641 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_641 (a k) (relation_zero k)
lemma reduced_642 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_642 (a k) (relation_zero k)
lemma reduced_643 : word (a k) [69, 8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_643 (a k) (relation_zero k)
lemma reduced_644 : word (a k) [70, 22, 3, 40, 60, 4, 54, 16, 58]=word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1] := by
  exact Universal.reduced_644 (a k) (relation_zero k)
lemma reduced_645 : word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_645 (a k) (relation_zero k)
lemma reduced_646 : word (a k) [70, 22, 3, 40, 60, 4, 54, 16, 59]=0 := by
  exact Universal.reduced_646 (a k) (relation_zero k)
lemma reduced_647 : word (a k) [32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_647 (a k) (relation_zero k)
lemma reduced_648 : word (a k) [39, 12, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_648 (a k) (relation_zero k)
lemma reduced_649 : word (a k) [7, 17, 21, 69, 8, 66, 24, 19, 52]=word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_649 (a k) (relation_zero k)
lemma reduced_650 : word (a k) [33, 13, 49, 69, 8, 66, 24, 19, 52]=word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_650 (a k) (relation_zero k)
lemma reduced_651 : word (a k) [50, 17, 21, 69, 8, 66, 24, 19, 52]=word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_651 (a k) (relation_zero k)
lemma reduced_652 : word (a k) [14, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_652 (a k) (relation_zero k)
lemma reduced_653 : word (a k) [18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_653 (a k) (relation_zero k)
lemma reduced_654 : word (a k) [60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.reduced_654 (a k) (relation_zero k)
lemma reduced_655 : word (a k) [12, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_655 (a k) (relation_zero k)
lemma reduced_656 : word (a k) [61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_656 (a k) (relation_zero k)
lemma reduced_657 : word (a k) [41, 43, 47, 7, 17, 21, 70, 22, 3]=word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 68] := by
  exact Universal.reduced_657 (a k) (relation_zero k)
lemma reduced_658 : word (a k) [55, 27, 58, 34, 63, 21, 70, 22, 3]=(-word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_658 (a k) (relation_zero k)
lemma reduced_659 : word (a k) [6, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_659 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
