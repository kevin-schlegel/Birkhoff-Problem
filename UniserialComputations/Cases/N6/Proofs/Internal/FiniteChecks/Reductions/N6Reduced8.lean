import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_480 : word v [67, 32, 62, 52, 42, 45, 6]=word v [67, 32, 61, 35, 56, 43, 47] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_480 v H)
lemma mul_reduced_480 (x : A) : word v [67, 32, 62, 52, 42, 45, 6]*x=(word v [67, 32, 61, 35, 56, 43, 47]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_480 v H)
lemma reduced_481 : word v [32, 61, 35, 56, 43, 47, 7]=word v [32, 61, 35, 55, 27, 59, 50] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_481 v H)
lemma mul_reduced_481 (x : A) : word v [32, 61, 35, 56, 43, 47, 7]*x=(word v [32, 61, 35, 55, 27, 59, 50]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_481 v H)
lemma reduced_482 : word v [39, 12, 35, 56, 43, 47, 7]=word v [39, 12, 35, 55, 27, 59, 50] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_482 v H)
lemma mul_reduced_482 (x : A) : word v [39, 12, 35, 56, 43, 47, 7]*x=(word v [39, 12, 35, 55, 27, 59, 50]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_482 v H)
lemma reduced_483 : word v [41, 43, 48, 51, 64, 36, 70]=word v [41, 43, 47, 7, 17, 21, 70] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_483 v H)
lemma mul_reduced_483 (x : A) : word v [41, 43, 48, 51, 64, 36, 70]*x=(word v [41, 43, 47, 7, 17, 21, 70]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_483 v H)
lemma reduced_484 : word v [55, 27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_484 v H)
lemma mul_reduced_484 (x : A) : word v [55, 27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_484 v H)
lemma reduced_485 : word v [12, 35, 55, 27, 59, 50, 17]=word v [12, 35, 55, 27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_485 v H)
lemma mul_reduced_485 (x : A) : word v [12, 35, 55, 27, 59, 50, 17]*x=(word v [12, 35, 55, 27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_485 v H)
lemma reduced_486 : word v [61, 35, 55, 27, 59, 50, 17]=word v [61, 35, 55, 27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_486 v H)
lemma mul_reduced_486 (x : A) : word v [61, 35, 55, 27, 59, 50, 17]*x=(word v [61, 35, 55, 27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_486 v H)
lemma reduced_487 : word v [31, 73, 67, 32, 62, 52, 41]=word v [31, 73, 67, 32, 61, 35, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_487 v H)
lemma mul_reduced_487 (x : A) : word v [31, 73, 67, 32, 62, 52, 41]*x=(word v [31, 73, 67, 32, 61, 35, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_487 v H)
lemma reduced_488 : word v [69, 8, 66, 24, 19, 53, 56]=word v [69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_488 v H)
lemma mul_reduced_488 (x : A) : word v [69, 8, 66, 24, 19, 53, 56]*x=(word v [69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_488 v H)
lemma reduced_489 : word v [70, 22, 3, 40, 62, 52, 41]=word v [70, 22, 3, 40, 60, 4, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_489 v H)
lemma mul_reduced_489 (x : A) : word v [70, 22, 3, 40, 62, 52, 41]*x=(word v [70, 22, 3, 40, 60, 4, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_489 v H)
lemma reduced_490 : word v [8, 66, 24, 19, 53, 54, 16]=word v [8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_490 v H)
lemma mul_reduced_490 (x : A) : word v [8, 66, 24, 19, 53, 54, 16]*x=(word v [8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_490 v H)
lemma reduced_491 : word v [22, 3, 40, 60, 4, 56, 44]=word v [22, 3, 40, 60, 4, 54, 16] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_491 v H)
lemma mul_reduced_491 (x : A) : word v [22, 3, 40, 60, 4, 56, 44]*x=(word v [22, 3, 40, 60, 4, 54, 16]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_491 v H)
lemma reduced_492 : word v [72, 37, 24, 19, 53, 54, 16]=word v [72, 37, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_492 v H)
lemma mul_reduced_492 (x : A) : word v [72, 37, 24, 19, 53, 54, 16]*x=(word v [72, 37, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_492 v H)
lemma reduced_493 : word v [73, 67, 32, 61, 35, 56, 44]=word v [73, 67, 32, 61, 35, 55, 27] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_493 v H)
lemma mul_reduced_493 (x : A) : word v [73, 67, 32, 61, 35, 56, 44]*x=(word v [73, 67, 32, 61, 35, 55, 27]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_493 v H)
lemma reduced_494 : word v [24, 18, 9, 41, 44, 58, 34]=word v [24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_494 v H)
lemma mul_reduced_494 (x : A) : word v [24, 18, 9, 41, 44, 58, 34]*x=(word v [24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_494 v H)
lemma reduced_495 : word v [28, 14, 9, 41, 44, 58, 34]=word v [28, 14, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_495 v H)
lemma mul_reduced_495 (x : A) : word v [28, 14, 9, 41, 44, 58, 34]*x=(word v [28, 14, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_495 v H)
lemma reduced_496 : word v [32, 61, 35, 55, 27, 59, 51]=word v [32, 61, 35, 55, 27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_496 v H)
lemma mul_reduced_496 (x : A) : word v [32, 61, 35, 55, 27, 59, 51]*x=(word v [32, 61, 35, 55, 27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_496 v H)
lemma reduced_497 : word v [39, 12, 35, 55, 27, 59, 51]=word v [39, 12, 35, 55, 27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_497 v H)
lemma mul_reduced_497 (x : A) : word v [39, 12, 35, 55, 27, 59, 51]*x=(word v [39, 12, 35, 55, 27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_497 v H)
lemma reduced_498 : word v [40, 60, 4, 54, 16, 57, 5]=word v [40, 60, 4, 54, 15, 1, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_498 v H)
lemma mul_reduced_498 (x : A) : word v [40, 60, 4, 54, 16, 57, 5]*x=(word v [40, 60, 4, 54, 15, 1, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_498 v H)
lemma reduced_499 : word v [21, 69, 8, 66, 25, 60, 4]=word v [21, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_499 v H)
lemma mul_reduced_499 (x : A) : word v [21, 69, 8, 66, 25, 60, 4]*x=(word v [21, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_499 v H)
lemma reduced_500 : word v [26, 31, 73, 67, 32, 62, 53]=word v [26, 31, 73, 67, 32, 61, 35] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_500 v H)
lemma mul_reduced_500 (x : A) : word v [26, 31, 73, 67, 32, 62, 53]*x=(word v [26, 31, 73, 67, 32, 61, 35]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_500 v H)
lemma reduced_501 : word v [36, 70, 22, 3, 40, 62, 53]=word v [36, 70, 22, 3, 40, 60, 4] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_501 v H)
lemma mul_reduced_501 (x : A) : word v [36, 70, 22, 3, 40, 62, 53]*x=(word v [36, 70, 22, 3, 40, 60, 4]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_501 v H)
lemma reduced_502 : word v [49, 69, 8, 66, 25, 60, 4]=word v [49, 69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_502 v H)
lemma mul_reduced_502 (x : A) : word v [49, 69, 8, 66, 25, 60, 4]*x=(word v [49, 69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_502 v H)
lemma reduced_503 : word v [4, 54, 15, 1, 34, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_503 v H)
lemma mul_reduced_503 (x : A) : word v [4, 54, 15, 1, 34, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_503 v H)
lemma reduced_504 : word v [9, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_504 v H)
lemma mul_reduced_504 (x : A) : word v [9, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_504 v H)
lemma reduced_505 : word v [35, 55, 27, 58, 34, 64, 36]=word v [35, 55, 27, 58, 34, 63, 21] + word v [35, 55, 27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_505 v H)
lemma mul_reduced_505 (x : A) : word v [35, 55, 27, 58, 34, 64, 36]*x=(word v [35, 55, 27, 58, 34, 63, 21]*x) + (word v [35, 55, 27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_505 v H)
lemma reduced_506 : word v [52, 41, 43, 48, 51, 65, 49]=(-word v [52, 41, 43, 47, 7, 17, 21]) + word v [52, 41, 43, 48, 51, 64, 36] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_506 v H)
lemma mul_reduced_506 (x : A) : word v [52, 41, 43, 48, 51, 65, 49]*x=(-(word v [52, 41, 43, 47, 7, 17, 21]*x)) + (word v [52, 41, 43, 48, 51, 64, 36]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_506 v H)
lemma reduced_507 : word v [52, 41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_507 v H)
lemma mul_reduced_507 (x : A) : word v [52, 41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_507 v H)
lemma reduced_508 : word v [7, 17, 21, 69, 8, 68, 40]=(-word v [7, 17, 21, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_508 v H)
lemma mul_reduced_508 (x : A) : word v [7, 17, 21, 69, 8, 68, 40]*x=(-(word v [7, 17, 21, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_508 v H)
lemma reduced_509 : word v [10, 11, 26, 31, 73, 68, 40]=word v [10, 11, 26, 31, 73, 67, 32] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_509 v H)
lemma mul_reduced_509 (x : A) : word v [10, 11, 26, 31, 73, 68, 40]*x=(word v [10, 11, 26, 31, 73, 67, 32]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_509 v H)
lemma reduced_510 : word v [33, 13, 49, 69, 8, 68, 40]=(-word v [33, 13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_510 v H)
lemma mul_reduced_510 (x : A) : word v [33, 13, 49, 69, 8, 68, 40]*x=(-(word v [33, 13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_510 v H)
lemma reduced_511 : word v [50, 17, 21, 69, 8, 68, 40]=(-word v [50, 17, 21, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_511 v H)
lemma mul_reduced_511 (x : A) : word v [50, 17, 21, 69, 8, 68, 40]*x=(-(word v [50, 17, 21, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_511 v H)
lemma reduced_512 : word v [27, 58, 33, 13, 49, 71, 73]=word v [27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_512 v H)
lemma mul_reduced_512 (x : A) : word v [27, 58, 33, 13, 49, 71, 73]*x=(word v [27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_512 v H)
lemma reduced_513 : word v [27, 58, 34, 63, 21, 70, 23]=word v [27, 58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_513 v H)
lemma mul_reduced_513 (x : A) : word v [27, 58, 34, 63, 21, 70, 23]*x=(word v [27, 58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_513 v H)
lemma reduced_514 : word v [43, 47, 7, 17, 21, 70, 23]=(-word v [43, 47, 7, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_514 v H)
lemma mul_reduced_514 (x : A) : word v [43, 47, 7, 17, 21, 70, 23]*x=(-(word v [43, 47, 7, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_514 v H)
lemma reduced_515 : word v [43, 48, 51, 64, 36, 71, 73]=(-word v [43, 47, 7, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_515 v H)
lemma mul_reduced_515 (x : A) : word v [43, 48, 51, 64, 36, 71, 73]*x=(-(word v [43, 47, 7, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_515 v H)
lemma reduced_516 : word v [45, 6, 7, 17, 21, 70, 23]=(-word v [45, 6, 7, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_516 v H)
lemma mul_reduced_516 (x : A) : word v [45, 6, 7, 17, 21, 70, 23]*x=(-(word v [45, 6, 7, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_516 v H)
lemma reduced_517 : word v [46, 48, 51, 64, 36, 71, 73]=(-word v [45, 6, 7, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_517 v H)
lemma mul_reduced_517 (x : A) : word v [46, 48, 51, 64, 36, 71, 73]*x=(-(word v [45, 6, 7, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_517 v H)
lemma reduced_518 : word v [48, 51, 64, 36, 71, 72, 37]=(-word v [47, 7, 17, 21, 69, 8, 66]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_518 v H)
lemma mul_reduced_518 (x : A) : word v [48, 51, 64, 36, 71, 72, 37]*x=(-(word v [47, 7, 17, 21, 69, 8, 66]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_518 v H)
lemma reduced_519 : word v [58, 33, 13, 49, 71, 72, 37]=word v [58, 33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_519 v H)
lemma mul_reduced_519 (x : A) : word v [58, 33, 13, 49, 71, 72, 37]*x=(word v [58, 33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_519 v H)
lemma reduced_520 : word v [74, 10, 11, 26, 31, 73, 66]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_520 v H)
lemma mul_reduced_520 (x : A) : word v [74, 10, 11, 26, 31, 73, 66]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_520 v H)
lemma reduced_521 : word v [3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_521 v H)
lemma mul_reduced_521 (x : A) : word v [3, 40, 60, 4, 54, 15, 1, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_521 v H)
lemma reduced_522 : word v [37, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_522 v H)
lemma mul_reduced_522 (x : A) : word v [37, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_522 v H)
lemma reduced_523 : word v [66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_523 v H)
lemma mul_reduced_523 (x : A) : word v [66, 24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_523 v H)
lemma reduced_524 : word v [24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_524 v H)
lemma mul_reduced_524 (x : A) : word v [24, 18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_524 v H)
lemma reduced_525 : word v [28, 14, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_525 v H)
lemma mul_reduced_525 (x : A) : word v [28, 14, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_525 v H)
lemma reduced_526 : word v [40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_526 v H)
lemma mul_reduced_526 (x : A) : word v [40, 60, 4, 54, 15, 1, 34, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_526 v H)
lemma reduced_527 : word v [6, 7, 17, 21, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_527 v H)
lemma mul_reduced_527 (x : A) : word v [6, 7, 17, 21, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_527 v H)
lemma reduced_528 : word v [47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_528 v H)
lemma mul_reduced_528 (x : A) : word v [47, 7, 17, 21, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_528 v H)
lemma reduced_529 : word v [58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_529 v H)
lemma mul_reduced_529 (x : A) : word v [58, 33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_529 v H)
lemma reduced_530 : word v [21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_530 v H)
lemma mul_reduced_530 (x : A) : word v [21, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_530 v H)
lemma reduced_531 : word v [36, 70, 22, 3, 40, 62, 52, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_531 v H)
lemma mul_reduced_531 (x : A) : word v [36, 70, 22, 3, 40, 62, 52, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_531 v H)
lemma reduced_532 : word v [21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_532 v H)
lemma mul_reduced_532 (x : A) : word v [21, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_532 v H)
lemma reduced_533 : word v [36, 70, 22, 3, 40, 60, 4, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_533 v H)
lemma mul_reduced_533 (x : A) : word v [36, 70, 22, 3, 40, 60, 4, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_533 v H)
lemma reduced_534 : word v [49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_534 v H)
lemma mul_reduced_534 (x : A) : word v [49, 69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_534 v H)
lemma reduced_535 : word v [69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_535 v H)
lemma mul_reduced_535 (x : A) : word v [69, 8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_535 v H)
lemma reduced_536 : word v [70, 22, 3, 40, 60, 4, 56, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_536 v H)
lemma mul_reduced_536 (x : A) : word v [70, 22, 3, 40, 60, 4, 56, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_536 v H)
lemma reduced_537 : word v [24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_537 v H)
lemma mul_reduced_537 (x : A) : word v [24, 18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_537 v H)
lemma reduced_538 : word v [28, 14, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_538 v H)
lemma mul_reduced_538 (x : A) : word v [28, 14, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_538 v H)
lemma reduced_539 : word v [40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_539 v H)
lemma mul_reduced_539 (x : A) : word v [40, 60, 4, 54, 15, 1, 34, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_539 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_480 : word (a k) [67, 32, 62, 52, 42, 45, 6]=word (a k) [67, 32, 61, 35, 56, 43, 47] := by
  exact Universal.reduced_480 (a k) (relation_zero k)
lemma reduced_481 : word (a k) [32, 61, 35, 56, 43, 47, 7]=word (a k) [32, 61, 35, 55, 27, 59, 50] := by
  exact Universal.reduced_481 (a k) (relation_zero k)
lemma reduced_482 : word (a k) [39, 12, 35, 56, 43, 47, 7]=word (a k) [39, 12, 35, 55, 27, 59, 50] := by
  exact Universal.reduced_482 (a k) (relation_zero k)
lemma reduced_483 : word (a k) [41, 43, 48, 51, 64, 36, 70]=word (a k) [41, 43, 47, 7, 17, 21, 70] := by
  exact Universal.reduced_483 (a k) (relation_zero k)
lemma reduced_484 : word (a k) [55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_484 (a k) (relation_zero k)
lemma reduced_485 : word (a k) [12, 35, 55, 27, 59, 50, 17]=word (a k) [12, 35, 55, 27, 58, 34, 63] := by
  exact Universal.reduced_485 (a k) (relation_zero k)
lemma reduced_486 : word (a k) [61, 35, 55, 27, 59, 50, 17]=word (a k) [61, 35, 55, 27, 58, 34, 63] := by
  exact Universal.reduced_486 (a k) (relation_zero k)
lemma reduced_487 : word (a k) [31, 73, 67, 32, 62, 52, 41]=word (a k) [31, 73, 67, 32, 61, 35, 56] := by
  exact Universal.reduced_487 (a k) (relation_zero k)
lemma reduced_488 : word (a k) [69, 8, 66, 24, 19, 53, 56]=word (a k) [69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_488 (a k) (relation_zero k)
lemma reduced_489 : word (a k) [70, 22, 3, 40, 62, 52, 41]=word (a k) [70, 22, 3, 40, 60, 4, 56] := by
  exact Universal.reduced_489 (a k) (relation_zero k)
lemma reduced_490 : word (a k) [8, 66, 24, 19, 53, 54, 16]=word (a k) [8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_490 (a k) (relation_zero k)
lemma reduced_491 : word (a k) [22, 3, 40, 60, 4, 56, 44]=word (a k) [22, 3, 40, 60, 4, 54, 16] := by
  exact Universal.reduced_491 (a k) (relation_zero k)
lemma reduced_492 : word (a k) [72, 37, 24, 19, 53, 54, 16]=word (a k) [72, 37, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_492 (a k) (relation_zero k)
lemma reduced_493 : word (a k) [73, 67, 32, 61, 35, 56, 44]=word (a k) [73, 67, 32, 61, 35, 55, 27] := by
  exact Universal.reduced_493 (a k) (relation_zero k)
lemma reduced_494 : word (a k) [24, 18, 9, 41, 44, 58, 34]=word (a k) [24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_494 (a k) (relation_zero k)
lemma reduced_495 : word (a k) [28, 14, 9, 41, 44, 58, 34]=word (a k) [28, 14, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_495 (a k) (relation_zero k)
lemma reduced_496 : word (a k) [32, 61, 35, 55, 27, 59, 51]=word (a k) [32, 61, 35, 55, 27, 58, 34] := by
  exact Universal.reduced_496 (a k) (relation_zero k)
lemma reduced_497 : word (a k) [39, 12, 35, 55, 27, 59, 51]=word (a k) [39, 12, 35, 55, 27, 58, 34] := by
  exact Universal.reduced_497 (a k) (relation_zero k)
lemma reduced_498 : word (a k) [40, 60, 4, 54, 16, 57, 5]=word (a k) [40, 60, 4, 54, 15, 1, 34] := by
  exact Universal.reduced_498 (a k) (relation_zero k)
lemma reduced_499 : word (a k) [21, 69, 8, 66, 25, 60, 4]=word (a k) [21, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_499 (a k) (relation_zero k)
lemma reduced_500 : word (a k) [26, 31, 73, 67, 32, 62, 53]=word (a k) [26, 31, 73, 67, 32, 61, 35] := by
  exact Universal.reduced_500 (a k) (relation_zero k)
lemma reduced_501 : word (a k) [36, 70, 22, 3, 40, 62, 53]=word (a k) [36, 70, 22, 3, 40, 60, 4] := by
  exact Universal.reduced_501 (a k) (relation_zero k)
lemma reduced_502 : word (a k) [49, 69, 8, 66, 25, 60, 4]=word (a k) [49, 69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_502 (a k) (relation_zero k)
lemma reduced_503 : word (a k) [4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.reduced_503 (a k) (relation_zero k)
lemma reduced_504 : word (a k) [9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_504 (a k) (relation_zero k)
lemma reduced_505 : word (a k) [35, 55, 27, 58, 34, 64, 36]=word (a k) [35, 55, 27, 58, 34, 63, 21] + word (a k) [35, 55, 27, 58, 33, 13, 49] := by
  exact Universal.reduced_505 (a k) (relation_zero k)
lemma reduced_506 : word (a k) [52, 41, 43, 48, 51, 65, 49]=(-word (a k) [52, 41, 43, 47, 7, 17, 21]) + word (a k) [52, 41, 43, 48, 51, 64, 36] := by
  exact Universal.reduced_506 (a k) (relation_zero k)
lemma reduced_507 : word (a k) [52, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_507 (a k) (relation_zero k)
lemma reduced_508 : word (a k) [7, 17, 21, 69, 8, 68, 40]=(-word (a k) [7, 17, 21, 69, 8, 66, 25]) := by
  exact Universal.reduced_508 (a k) (relation_zero k)
lemma reduced_509 : word (a k) [10, 11, 26, 31, 73, 68, 40]=word (a k) [10, 11, 26, 31, 73, 67, 32] := by
  exact Universal.reduced_509 (a k) (relation_zero k)
lemma reduced_510 : word (a k) [33, 13, 49, 69, 8, 68, 40]=(-word (a k) [33, 13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_510 (a k) (relation_zero k)
lemma reduced_511 : word (a k) [50, 17, 21, 69, 8, 68, 40]=(-word (a k) [50, 17, 21, 69, 8, 66, 25]) := by
  exact Universal.reduced_511 (a k) (relation_zero k)
lemma reduced_512 : word (a k) [27, 58, 33, 13, 49, 71, 73]=word (a k) [27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_512 (a k) (relation_zero k)
lemma reduced_513 : word (a k) [27, 58, 34, 63, 21, 70, 23]=word (a k) [27, 58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_513 (a k) (relation_zero k)
lemma reduced_514 : word (a k) [43, 47, 7, 17, 21, 70, 23]=(-word (a k) [43, 47, 7, 17, 21, 69, 8]) := by
  exact Universal.reduced_514 (a k) (relation_zero k)
lemma reduced_515 : word (a k) [43, 48, 51, 64, 36, 71, 73]=(-word (a k) [43, 47, 7, 17, 21, 69, 8]) := by
  exact Universal.reduced_515 (a k) (relation_zero k)
lemma reduced_516 : word (a k) [45, 6, 7, 17, 21, 70, 23]=(-word (a k) [45, 6, 7, 17, 21, 69, 8]) := by
  exact Universal.reduced_516 (a k) (relation_zero k)
lemma reduced_517 : word (a k) [46, 48, 51, 64, 36, 71, 73]=(-word (a k) [45, 6, 7, 17, 21, 69, 8]) := by
  exact Universal.reduced_517 (a k) (relation_zero k)
lemma reduced_518 : word (a k) [48, 51, 64, 36, 71, 72, 37]=(-word (a k) [47, 7, 17, 21, 69, 8, 66]) := by
  exact Universal.reduced_518 (a k) (relation_zero k)
lemma reduced_519 : word (a k) [58, 33, 13, 49, 71, 72, 37]=word (a k) [58, 33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_519 (a k) (relation_zero k)
lemma reduced_520 : word (a k) [74, 10, 11, 26, 31, 73, 66]=0 := by
  exact Universal.reduced_520 (a k) (relation_zero k)
lemma reduced_521 : word (a k) [3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  exact Universal.reduced_521 (a k) (relation_zero k)
lemma reduced_522 : word (a k) [37, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_522 (a k) (relation_zero k)
lemma reduced_523 : word (a k) [66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_523 (a k) (relation_zero k)
lemma reduced_524 : word (a k) [24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_524 (a k) (relation_zero k)
lemma reduced_525 : word (a k) [28, 14, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_525 (a k) (relation_zero k)
lemma reduced_526 : word (a k) [40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.reduced_526 (a k) (relation_zero k)
lemma reduced_527 : word (a k) [6, 7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_527 (a k) (relation_zero k)
lemma reduced_528 : word (a k) [47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_528 (a k) (relation_zero k)
lemma reduced_529 : word (a k) [58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_529 (a k) (relation_zero k)
lemma reduced_530 : word (a k) [21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_530 (a k) (relation_zero k)
lemma reduced_531 : word (a k) [36, 70, 22, 3, 40, 62, 52, 42]=0 := by
  exact Universal.reduced_531 (a k) (relation_zero k)
lemma reduced_532 : word (a k) [21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_532 (a k) (relation_zero k)
lemma reduced_533 : word (a k) [36, 70, 22, 3, 40, 60, 4, 55]=0 := by
  exact Universal.reduced_533 (a k) (relation_zero k)
lemma reduced_534 : word (a k) [49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_534 (a k) (relation_zero k)
lemma reduced_535 : word (a k) [69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_535 (a k) (relation_zero k)
lemma reduced_536 : word (a k) [70, 22, 3, 40, 60, 4, 56, 43]=0 := by
  exact Universal.reduced_536 (a k) (relation_zero k)
lemma reduced_537 : word (a k) [24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_537 (a k) (relation_zero k)
lemma reduced_538 : word (a k) [28, 14, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_538 (a k) (relation_zero k)
lemma reduced_539 : word (a k) [40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.reduced_539 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
