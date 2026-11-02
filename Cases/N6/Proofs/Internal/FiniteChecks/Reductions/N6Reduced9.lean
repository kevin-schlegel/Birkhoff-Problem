import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_540 : word v [27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_540 v H)
lemma mul_reduced_540 (x : A) : word v [27, 58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_540 v H)
lemma reduced_541 : word v [43, 47, 7, 17, 21, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_541 v H)
lemma mul_reduced_541 (x : A) : word v [43, 47, 7, 17, 21, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_541 v H)
lemma reduced_542 : word v [45, 6, 7, 17, 21, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_542 v H)
lemma mul_reduced_542 (x : A) : word v [45, 6, 7, 17, 21, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_542 v H)
lemma reduced_543 : word v [49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_543 v H)
lemma mul_reduced_543 (x : A) : word v [49, 69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_543 v H)
lemma reduced_544 : word v [8, 66, 24, 19, 53, 54, 15, 1]=word v [8, 66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_544 v H)
lemma mul_reduced_544 (x : A) : word v [8, 66, 24, 19, 53, 54, 15, 1]*x=(word v [8, 66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_544 v H)
lemma reduced_545 : word v [22, 3, 40, 60, 4, 54, 16, 58]=word v [22, 3, 40, 60, 4, 54, 15, 1] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_545 v H)
lemma mul_reduced_545 (x : A) : word v [22, 3, 40, 60, 4, 54, 16, 58]*x=(word v [22, 3, 40, 60, 4, 54, 15, 1]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_545 v H)
lemma reduced_546 : word v [72, 37, 24, 19, 53, 54, 15, 1]=word v [72, 37, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_546 v H)
lemma mul_reduced_546 (x : A) : word v [72, 37, 24, 19, 53, 54, 15, 1]*x=(word v [72, 37, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_546 v H)
lemma reduced_547 : word v [8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_547 v H)
lemma mul_reduced_547 (x : A) : word v [8, 66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_547 v H)
lemma reduced_548 : word v [22, 3, 40, 60, 4, 54, 16, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_548 v H)
lemma mul_reduced_548 (x : A) : word v [22, 3, 40, 60, 4, 54, 16, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_548 v H)
lemma reduced_549 : word v [72, 37, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_549 v H)
lemma mul_reduced_549 (x : A) : word v [72, 37, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_549 v H)
lemma reduced_550 : word v [12, 35, 55, 27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_550 v H)
lemma mul_reduced_550 (x : A) : word v [12, 35, 55, 27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_550 v H)
lemma reduced_551 : word v [61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_551 v H)
lemma mul_reduced_551 (x : A) : word v [61, 35, 55, 27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_551 v H)
lemma reduced_552 : word v [13, 49, 69, 8, 66, 24, 19, 52]=word v [13, 49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_552 v H)
lemma mul_reduced_552 (x : A) : word v [13, 49, 69, 8, 66, 24, 19, 52]*x=(word v [13, 49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_552 v H)
lemma reduced_553 : word v [17, 21, 69, 8, 66, 24, 19, 52]=word v [17, 21, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_553 v H)
lemma mul_reduced_553 (x : A) : word v [17, 21, 69, 8, 66, 24, 19, 52]*x=(word v [17, 21, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_553 v H)
lemma reduced_554 : word v [63, 21, 69, 8, 66, 24, 19, 52]=word v [63, 21, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_554 v H)
lemma mul_reduced_554 (x : A) : word v [63, 21, 69, 8, 66, 24, 19, 52]*x=(word v [63, 21, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_554 v H)
lemma reduced_555 : word v [4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_555 v H)
lemma mul_reduced_555 (x : A) : word v [4, 54, 15, 1, 34, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_555 v H)
lemma reduced_556 : word v [9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_556 v H)
lemma mul_reduced_556 (x : A) : word v [9, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_556 v H)
lemma reduced_557 : word v [52, 41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_557 v H)
lemma mul_reduced_557 (x : A) : word v [52, 41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_557 v H)
lemma reduced_558 : word v [35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_558 v H)
lemma mul_reduced_558 (x : A) : word v [35, 55, 27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_558 v H)
lemma reduced_559 : word v [52, 41, 43, 47, 7, 17, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_559 v H)
lemma mul_reduced_559 (x : A) : word v [52, 41, 43, 47, 7, 17, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_559 v H)
lemma reduced_560 : word v [27, 58, 34, 63, 21, 70, 22, 3]=(-word v [27, 58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_560 v H)
lemma mul_reduced_560 (x : A) : word v [27, 58, 34, 63, 21, 70, 22, 3]*x=(-(word v [27, 58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_560 v H)
lemma reduced_561 : word v [43, 47, 7, 17, 21, 70, 22, 3]=word v [43, 47, 7, 17, 21, 69, 8, 68] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_561 v H)
lemma mul_reduced_561 (x : A) : word v [43, 47, 7, 17, 21, 70, 22, 3]*x=(word v [43, 47, 7, 17, 21, 69, 8, 68]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_561 v H)
lemma reduced_562 : word v [45, 6, 7, 17, 21, 70, 22, 3]=word v [45, 6, 7, 17, 21, 69, 8, 68] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_562 v H)
lemma mul_reduced_562 (x : A) : word v [45, 6, 7, 17, 21, 70, 22, 3]*x=(word v [45, 6, 7, 17, 21, 69, 8, 68]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_562 v H)
lemma reduced_563 : word v [7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_563 v H)
lemma mul_reduced_563 (x : A) : word v [7, 17, 21, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_563 v H)
lemma reduced_564 : word v [33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_564 v H)
lemma mul_reduced_564 (x : A) : word v [33, 13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_564 v H)
lemma reduced_565 : word v [50, 17, 21, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_565 v H)
lemma mul_reduced_565 (x : A) : word v [50, 17, 21, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_565 v H)
lemma reduced_566 : word v [7, 17, 21, 69, 8, 66, 25, 62]=word v [7, 17, 21, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_566 v H)
lemma mul_reduced_566 (x : A) : word v [7, 17, 21, 69, 8, 66, 25, 62]*x=(word v [7, 17, 21, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_566 v H)
lemma reduced_567 : word v [33, 13, 49, 69, 8, 66, 25, 62]=word v [33, 13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_567 v H)
lemma mul_reduced_567 (x : A) : word v [33, 13, 49, 69, 8, 66, 25, 62]*x=(word v [33, 13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_567 v H)
lemma reduced_568 : word v [50, 17, 21, 69, 8, 66, 25, 62]=word v [50, 17, 21, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_568 v H)
lemma mul_reduced_568 (x : A) : word v [50, 17, 21, 69, 8, 66, 25, 62]*x=(word v [50, 17, 21, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_568 v H)
lemma reduced_569 : word v [73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_569 v H)
lemma mul_reduced_569 (x : A) : word v [73, 67, 32, 61, 35, 55, 27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_569 v H)
lemma reduced_570 : word v [33, 13, 49, 71, 72, 38, 28, 14]=word v [33, 13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_570 v H)
lemma mul_reduced_570 (x : A) : word v [33, 13, 49, 71, 72, 38, 28, 14]*x=(word v [33, 13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_570 v H)
lemma reduced_571 : word v [51, 64, 36, 71, 72, 38, 28, 14]=(-word v [50, 17, 21, 69, 8, 66, 24, 18]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_571 v H)
lemma mul_reduced_571 (x : A) : word v [51, 64, 36, 71, 72, 38, 28, 14]*x=(-(word v [50, 17, 21, 69, 8, 66, 24, 18]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_571 v H)
lemma reduced_572 : word v [10, 11, 26, 31, 73, 67, 32, 60]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_572 v H)
lemma mul_reduced_572 (x : A) : word v [10, 11, 26, 31, 73, 67, 32, 60]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_572 v H)
lemma reduced_573 : word v [32, 61, 35, 55, 27, 58, 34, 65]=word v [32, 61, 35, 55, 27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_573 v H)
lemma mul_reduced_573 (x : A) : word v [32, 61, 35, 55, 27, 58, 34, 65]*x=(word v [32, 61, 35, 55, 27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_573 v H)
lemma reduced_574 : word v [39, 12, 35, 55, 27, 58, 34, 65]=word v [39, 12, 35, 55, 27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_574 v H)
lemma mul_reduced_574 (x : A) : word v [39, 12, 35, 55, 27, 58, 34, 65]*x=(word v [39, 12, 35, 55, 27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_574 v H)
lemma reduced_575 : word v [26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_575 v H)
lemma mul_reduced_575 (x : A) : word v [26, 31, 73, 67, 32, 61, 35, 54]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_575 v H)
lemma reduced_576 : word v [35, 55, 27, 58, 34, 63, 21, 69]=(-word v [35, 55, 27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_576 v H)
lemma mul_reduced_576 (x : A) : word v [35, 55, 27, 58, 34, 63, 21, 69]*x=(-(word v [35, 55, 27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_576 v H)
lemma reduced_577 : word v [52, 41, 43, 48, 51, 64, 36, 69]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_577 v H)
lemma mul_reduced_577 (x : A) : word v [52, 41, 43, 48, 51, 64, 36, 69]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_577 v H)
lemma reduced_578 : word v [48, 51, 64, 36, 71, 72, 38, 29]=(-word v [47, 7, 17, 21, 69, 8, 66, 24]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_578 v H)
lemma mul_reduced_578 (x : A) : word v [48, 51, 64, 36, 71, 72, 38, 29]*x=(-(word v [47, 7, 17, 21, 69, 8, 66, 24]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_578 v H)
lemma reduced_579 : word v [58, 33, 13, 49, 71, 72, 38, 29]=word v [58, 33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_579 v H)
lemma mul_reduced_579 (x : A) : word v [58, 33, 13, 49, 71, 72, 38, 29]*x=(word v [58, 33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_579 v H)
lemma reduced_580 : word v [10, 11, 26, 31, 73, 68, 39, 12]=word v [10, 11, 26, 31, 73, 67, 32, 61] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_580 v H)
lemma mul_reduced_580 (x : A) : word v [10, 11, 26, 31, 73, 68, 39, 12]*x=(word v [10, 11, 26, 31, 73, 67, 32, 61]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_580 v H)
lemma reduced_581 : word v [31, 73, 67, 32, 62, 52, 42, 46]=word v [31, 73, 67, 32, 61, 35, 56, 43] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_581 v H)
lemma mul_reduced_581 (x : A) : word v [31, 73, 67, 32, 62, 52, 42, 46]*x=(word v [31, 73, 67, 32, 61, 35, 56, 43]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_581 v H)
lemma reduced_582 : word v [73, 67, 32, 61, 35, 56, 43, 48]=word v [73, 67, 32, 61, 35, 55, 27, 59] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_582 v H)
lemma mul_reduced_582 (x : A) : word v [73, 67, 32, 61, 35, 56, 43, 48]*x=(word v [73, 67, 32, 61, 35, 55, 27, 59]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_582 v H)
lemma reduced_583 : word v [73, 67, 32, 62, 52, 42, 45, 6]=word v [73, 67, 32, 61, 35, 56, 43, 47] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_583 v H)
lemma mul_reduced_583 (x : A) : word v [73, 67, 32, 62, 52, 42, 45, 6]*x=(word v [73, 67, 32, 61, 35, 56, 43, 47]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_583 v H)
lemma reduced_584 : word v [67, 32, 61, 35, 56, 43, 47, 7]=word v [67, 32, 61, 35, 55, 27, 59, 50] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_584 v H)
lemma mul_reduced_584 (x : A) : word v [67, 32, 61, 35, 56, 43, 47, 7]*x=(word v [67, 32, 61, 35, 55, 27, 59, 50]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_584 v H)
lemma reduced_585 : word v [35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_585 v H)
lemma mul_reduced_585 (x : A) : word v [35, 55, 27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_585 v H)
lemma reduced_586 : word v [52, 41, 43, 48, 51, 64, 36, 70]=word v [52, 41, 43, 47, 7, 17, 21, 70] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_586 v H)
lemma mul_reduced_586 (x : A) : word v [52, 41, 43, 48, 51, 64, 36, 70]*x=(word v [52, 41, 43, 47, 7, 17, 21, 70]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_586 v H)
lemma reduced_587 : word v [32, 61, 35, 55, 27, 59, 50, 17]=word v [32, 61, 35, 55, 27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_587 v H)
lemma mul_reduced_587 (x : A) : word v [32, 61, 35, 55, 27, 59, 50, 17]*x=(word v [32, 61, 35, 55, 27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_587 v H)
lemma reduced_588 : word v [39, 12, 35, 55, 27, 59, 50, 17]=word v [39, 12, 35, 55, 27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_588 v H)
lemma mul_reduced_588 (x : A) : word v [39, 12, 35, 55, 27, 59, 50, 17]*x=(word v [39, 12, 35, 55, 27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_588 v H)
lemma reduced_589 : word v [21, 69, 8, 66, 24, 19, 53, 56]=word v [21, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_589 v H)
lemma mul_reduced_589 (x : A) : word v [21, 69, 8, 66, 24, 19, 53, 56]*x=(word v [21, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_589 v H)
lemma reduced_590 : word v [26, 31, 73, 67, 32, 62, 52, 41]=word v [26, 31, 73, 67, 32, 61, 35, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_590 v H)
lemma mul_reduced_590 (x : A) : word v [26, 31, 73, 67, 32, 62, 52, 41]*x=(word v [26, 31, 73, 67, 32, 61, 35, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_590 v H)
lemma reduced_591 : word v [36, 70, 22, 3, 40, 62, 52, 41]=word v [36, 70, 22, 3, 40, 60, 4, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_591 v H)
lemma mul_reduced_591 (x : A) : word v [36, 70, 22, 3, 40, 62, 52, 41]*x=(word v [36, 70, 22, 3, 40, 60, 4, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_591 v H)
lemma reduced_592 : word v [49, 69, 8, 66, 24, 19, 53, 56]=word v [49, 69, 8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_592 v H)
lemma mul_reduced_592 (x : A) : word v [49, 69, 8, 66, 24, 19, 53, 56]*x=(word v [49, 69, 8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_592 v H)
lemma reduced_593 : word v [31, 73, 67, 32, 61, 35, 56, 44]=word v [31, 73, 67, 32, 61, 35, 55, 27] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_593 v H)
lemma mul_reduced_593 (x : A) : word v [31, 73, 67, 32, 61, 35, 56, 44]*x=(word v [31, 73, 67, 32, 61, 35, 55, 27]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_593 v H)
lemma reduced_594 : word v [69, 8, 66, 24, 19, 53, 54, 16]=word v [69, 8, 66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_594 v H)
lemma mul_reduced_594 (x : A) : word v [69, 8, 66, 24, 19, 53, 54, 16]*x=(word v [69, 8, 66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_594 v H)
lemma reduced_595 : word v [70, 22, 3, 40, 60, 4, 56, 44]=word v [70, 22, 3, 40, 60, 4, 54, 16] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_595 v H)
lemma mul_reduced_595 (x : A) : word v [70, 22, 3, 40, 60, 4, 56, 44]*x=(word v [70, 22, 3, 40, 60, 4, 54, 16]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_595 v H)
lemma reduced_596 : word v [3, 40, 60, 4, 54, 16, 57, 5]=word v [3, 40, 60, 4, 54, 15, 1, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_596 v H)
lemma mul_reduced_596 (x : A) : word v [3, 40, 60, 4, 54, 16, 57, 5]*x=(word v [3, 40, 60, 4, 54, 15, 1, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_596 v H)
lemma reduced_597 : word v [37, 24, 18, 9, 41, 44, 58, 34]=word v [37, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_597 v H)
lemma mul_reduced_597 (x : A) : word v [37, 24, 18, 9, 41, 44, 58, 34]*x=(word v [37, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_597 v H)
lemma reduced_598 : word v [66, 24, 18, 9, 41, 44, 58, 34]=word v [66, 24, 18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_598 v H)
lemma mul_reduced_598 (x : A) : word v [66, 24, 18, 9, 41, 44, 58, 34]*x=(word v [66, 24, 18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_598 v H)
lemma reduced_599 : word v [67, 32, 61, 35, 55, 27, 59, 51]=word v [67, 32, 61, 35, 55, 27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_599 v H)
lemma mul_reduced_599 (x : A) : word v [67, 32, 61, 35, 55, 27, 59, 51]*x=(word v [67, 32, 61, 35, 55, 27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_599 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_540 : word (a k) [27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_540 (a k) (relation_zero k)
lemma reduced_541 : word (a k) [43, 47, 7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.reduced_541 (a k) (relation_zero k)
lemma reduced_542 : word (a k) [45, 6, 7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.reduced_542 (a k) (relation_zero k)
lemma reduced_543 : word (a k) [49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_543 (a k) (relation_zero k)
lemma reduced_544 : word (a k) [8, 66, 24, 19, 53, 54, 15, 1]=word (a k) [8, 66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_544 (a k) (relation_zero k)
lemma reduced_545 : word (a k) [22, 3, 40, 60, 4, 54, 16, 58]=word (a k) [22, 3, 40, 60, 4, 54, 15, 1] := by
  exact Universal.reduced_545 (a k) (relation_zero k)
lemma reduced_546 : word (a k) [72, 37, 24, 19, 53, 54, 15, 1]=word (a k) [72, 37, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_546 (a k) (relation_zero k)
lemma reduced_547 : word (a k) [8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_547 (a k) (relation_zero k)
lemma reduced_548 : word (a k) [22, 3, 40, 60, 4, 54, 16, 59]=0 := by
  exact Universal.reduced_548 (a k) (relation_zero k)
lemma reduced_549 : word (a k) [72, 37, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_549 (a k) (relation_zero k)
lemma reduced_550 : word (a k) [12, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_550 (a k) (relation_zero k)
lemma reduced_551 : word (a k) [61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_551 (a k) (relation_zero k)
lemma reduced_552 : word (a k) [13, 49, 69, 8, 66, 24, 19, 52]=word (a k) [13, 49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_552 (a k) (relation_zero k)
lemma reduced_553 : word (a k) [17, 21, 69, 8, 66, 24, 19, 52]=word (a k) [17, 21, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_553 (a k) (relation_zero k)
lemma reduced_554 : word (a k) [63, 21, 69, 8, 66, 24, 19, 52]=word (a k) [63, 21, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_554 (a k) (relation_zero k)
lemma reduced_555 : word (a k) [4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.reduced_555 (a k) (relation_zero k)
lemma reduced_556 : word (a k) [9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_556 (a k) (relation_zero k)
lemma reduced_557 : word (a k) [52, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_557 (a k) (relation_zero k)
lemma reduced_558 : word (a k) [35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_558 (a k) (relation_zero k)
lemma reduced_559 : word (a k) [52, 41, 43, 47, 7, 17, 21, 71]=0 := by
  exact Universal.reduced_559 (a k) (relation_zero k)
lemma reduced_560 : word (a k) [27, 58, 34, 63, 21, 70, 22, 3]=(-word (a k) [27, 58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_560 (a k) (relation_zero k)
lemma reduced_561 : word (a k) [43, 47, 7, 17, 21, 70, 22, 3]=word (a k) [43, 47, 7, 17, 21, 69, 8, 68] := by
  exact Universal.reduced_561 (a k) (relation_zero k)
lemma reduced_562 : word (a k) [45, 6, 7, 17, 21, 70, 22, 3]=word (a k) [45, 6, 7, 17, 21, 69, 8, 68] := by
  exact Universal.reduced_562 (a k) (relation_zero k)
lemma reduced_563 : word (a k) [7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_563 (a k) (relation_zero k)
lemma reduced_564 : word (a k) [33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_564 (a k) (relation_zero k)
lemma reduced_565 : word (a k) [50, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_565 (a k) (relation_zero k)
lemma reduced_566 : word (a k) [7, 17, 21, 69, 8, 66, 25, 62]=word (a k) [7, 17, 21, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_566 (a k) (relation_zero k)
lemma reduced_567 : word (a k) [33, 13, 49, 69, 8, 66, 25, 62]=word (a k) [33, 13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_567 (a k) (relation_zero k)
lemma reduced_568 : word (a k) [50, 17, 21, 69, 8, 66, 25, 62]=word (a k) [50, 17, 21, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_568 (a k) (relation_zero k)
lemma reduced_569 : word (a k) [73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.reduced_569 (a k) (relation_zero k)
lemma reduced_570 : word (a k) [33, 13, 49, 71, 72, 38, 28, 14]=word (a k) [33, 13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_570 (a k) (relation_zero k)
lemma reduced_571 : word (a k) [51, 64, 36, 71, 72, 38, 28, 14]=(-word (a k) [50, 17, 21, 69, 8, 66, 24, 18]) := by
  exact Universal.reduced_571 (a k) (relation_zero k)
lemma reduced_572 : word (a k) [10, 11, 26, 31, 73, 67, 32, 60]=0 := by
  exact Universal.reduced_572 (a k) (relation_zero k)
lemma reduced_573 : word (a k) [32, 61, 35, 55, 27, 58, 34, 65]=word (a k) [32, 61, 35, 55, 27, 58, 33, 13] := by
  exact Universal.reduced_573 (a k) (relation_zero k)
lemma reduced_574 : word (a k) [39, 12, 35, 55, 27, 58, 34, 65]=word (a k) [39, 12, 35, 55, 27, 58, 33, 13] := by
  exact Universal.reduced_574 (a k) (relation_zero k)
lemma reduced_575 : word (a k) [26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  exact Universal.reduced_575 (a k) (relation_zero k)
lemma reduced_576 : word (a k) [35, 55, 27, 58, 34, 63, 21, 69]=(-word (a k) [35, 55, 27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_576 (a k) (relation_zero k)
lemma reduced_577 : word (a k) [52, 41, 43, 48, 51, 64, 36, 69]=0 := by
  exact Universal.reduced_577 (a k) (relation_zero k)
lemma reduced_578 : word (a k) [48, 51, 64, 36, 71, 72, 38, 29]=(-word (a k) [47, 7, 17, 21, 69, 8, 66, 24]) := by
  exact Universal.reduced_578 (a k) (relation_zero k)
lemma reduced_579 : word (a k) [58, 33, 13, 49, 71, 72, 38, 29]=word (a k) [58, 33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_579 (a k) (relation_zero k)
lemma reduced_580 : word (a k) [10, 11, 26, 31, 73, 68, 39, 12]=word (a k) [10, 11, 26, 31, 73, 67, 32, 61] := by
  exact Universal.reduced_580 (a k) (relation_zero k)
lemma reduced_581 : word (a k) [31, 73, 67, 32, 62, 52, 42, 46]=word (a k) [31, 73, 67, 32, 61, 35, 56, 43] := by
  exact Universal.reduced_581 (a k) (relation_zero k)
lemma reduced_582 : word (a k) [73, 67, 32, 61, 35, 56, 43, 48]=word (a k) [73, 67, 32, 61, 35, 55, 27, 59] := by
  exact Universal.reduced_582 (a k) (relation_zero k)
lemma reduced_583 : word (a k) [73, 67, 32, 62, 52, 42, 45, 6]=word (a k) [73, 67, 32, 61, 35, 56, 43, 47] := by
  exact Universal.reduced_583 (a k) (relation_zero k)
lemma reduced_584 : word (a k) [67, 32, 61, 35, 56, 43, 47, 7]=word (a k) [67, 32, 61, 35, 55, 27, 59, 50] := by
  exact Universal.reduced_584 (a k) (relation_zero k)
lemma reduced_585 : word (a k) [35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_585 (a k) (relation_zero k)
lemma reduced_586 : word (a k) [52, 41, 43, 48, 51, 64, 36, 70]=word (a k) [52, 41, 43, 47, 7, 17, 21, 70] := by
  exact Universal.reduced_586 (a k) (relation_zero k)
lemma reduced_587 : word (a k) [32, 61, 35, 55, 27, 59, 50, 17]=word (a k) [32, 61, 35, 55, 27, 58, 34, 63] := by
  exact Universal.reduced_587 (a k) (relation_zero k)
lemma reduced_588 : word (a k) [39, 12, 35, 55, 27, 59, 50, 17]=word (a k) [39, 12, 35, 55, 27, 58, 34, 63] := by
  exact Universal.reduced_588 (a k) (relation_zero k)
lemma reduced_589 : word (a k) [21, 69, 8, 66, 24, 19, 53, 56]=word (a k) [21, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_589 (a k) (relation_zero k)
lemma reduced_590 : word (a k) [26, 31, 73, 67, 32, 62, 52, 41]=word (a k) [26, 31, 73, 67, 32, 61, 35, 56] := by
  exact Universal.reduced_590 (a k) (relation_zero k)
lemma reduced_591 : word (a k) [36, 70, 22, 3, 40, 62, 52, 41]=word (a k) [36, 70, 22, 3, 40, 60, 4, 56] := by
  exact Universal.reduced_591 (a k) (relation_zero k)
lemma reduced_592 : word (a k) [49, 69, 8, 66, 24, 19, 53, 56]=word (a k) [49, 69, 8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_592 (a k) (relation_zero k)
lemma reduced_593 : word (a k) [31, 73, 67, 32, 61, 35, 56, 44]=word (a k) [31, 73, 67, 32, 61, 35, 55, 27] := by
  exact Universal.reduced_593 (a k) (relation_zero k)
lemma reduced_594 : word (a k) [69, 8, 66, 24, 19, 53, 54, 16]=word (a k) [69, 8, 66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_594 (a k) (relation_zero k)
lemma reduced_595 : word (a k) [70, 22, 3, 40, 60, 4, 56, 44]=word (a k) [70, 22, 3, 40, 60, 4, 54, 16] := by
  exact Universal.reduced_595 (a k) (relation_zero k)
lemma reduced_596 : word (a k) [3, 40, 60, 4, 54, 16, 57, 5]=word (a k) [3, 40, 60, 4, 54, 15, 1, 34] := by
  exact Universal.reduced_596 (a k) (relation_zero k)
lemma reduced_597 : word (a k) [37, 24, 18, 9, 41, 44, 58, 34]=word (a k) [37, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_597 (a k) (relation_zero k)
lemma reduced_598 : word (a k) [66, 24, 18, 9, 41, 44, 58, 34]=word (a k) [66, 24, 18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_598 (a k) (relation_zero k)
lemma reduced_599 : word (a k) [67, 32, 61, 35, 55, 27, 59, 51]=word (a k) [67, 32, 61, 35, 55, 27, 58, 34] := by
  exact Universal.reduced_599 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
