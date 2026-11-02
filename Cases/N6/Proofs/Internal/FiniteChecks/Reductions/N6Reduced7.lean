import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_420 : word v [24, 18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_420 v H)
lemma mul_reduced_420 (x : A) : word v [24, 18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_420 v H)
lemma reduced_421 : word v [28, 14, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_421 v H)
lemma mul_reduced_421 (x : A) : word v [28, 14, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_421 v H)
lemma reduced_422 : word v [40, 60, 4, 54, 15, 1, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_422 v H)
lemma mul_reduced_422 (x : A) : word v [40, 60, 4, 54, 15, 1, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_422 v H)
lemma reduced_423 : word v [18, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_423 v H)
lemma mul_reduced_423 (x : A) : word v [18, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_423 v H)
lemma reduced_424 : word v [60, 4, 54, 15, 1, 34, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_424 v H)
lemma mul_reduced_424 (x : A) : word v [60, 4, 54, 15, 1, 34, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_424 v H)
lemma reduced_425 : word v [7, 17, 21, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_425 v H)
lemma mul_reduced_425 (x : A) : word v [7, 17, 21, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_425 v H)
lemma reduced_426 : word v [33, 13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_426 v H)
lemma mul_reduced_426 (x : A) : word v [33, 13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_426 v H)
lemma reduced_427 : word v [50, 17, 21, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_427 v H)
lemma mul_reduced_427 (x : A) : word v [50, 17, 21, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_427 v H)
lemma reduced_428 : word v [70, 22, 3, 40, 62, 52, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_428 v H)
lemma mul_reduced_428 (x : A) : word v [70, 22, 3, 40, 62, 52, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_428 v H)
lemma reduced_429 : word v [69, 8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_429 v H)
lemma mul_reduced_429 (x : A) : word v [69, 8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_429 v H)
lemma reduced_430 : word v [70, 22, 3, 40, 60, 4, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_430 v H)
lemma mul_reduced_430 (x : A) : word v [70, 22, 3, 40, 60, 4, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_430 v H)
lemma reduced_431 : word v [8, 66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_431 v H)
lemma mul_reduced_431 (x : A) : word v [8, 66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_431 v H)
lemma reduced_432 : word v [22, 3, 40, 60, 4, 56, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_432 v H)
lemma mul_reduced_432 (x : A) : word v [22, 3, 40, 60, 4, 56, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_432 v H)
lemma reduced_433 : word v [72, 37, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_433 v H)
lemma mul_reduced_433 (x : A) : word v [72, 37, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_433 v H)
lemma reduced_434 : word v [14, 9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_434 v H)
lemma mul_reduced_434 (x : A) : word v [14, 9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_434 v H)
lemma reduced_435 : word v [14, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_435 v H)
lemma mul_reduced_435 (x : A) : word v [14, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_435 v H)
lemma reduced_436 : word v [18, 9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_436 v H)
lemma mul_reduced_436 (x : A) : word v [18, 9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_436 v H)
lemma reduced_437 : word v [60, 4, 54, 15, 1, 34, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_437 v H)
lemma mul_reduced_437 (x : A) : word v [60, 4, 54, 15, 1, 34, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_437 v H)
lemma reduced_438 : word v [6, 7, 17, 21, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_438 v H)
lemma mul_reduced_438 (x : A) : word v [6, 7, 17, 21, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_438 v H)
lemma reduced_439 : word v [47, 7, 17, 21, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_439 v H)
lemma mul_reduced_439 (x : A) : word v [47, 7, 17, 21, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_439 v H)
lemma reduced_440 : word v [58, 33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_440 v H)
lemma mul_reduced_440 (x : A) : word v [58, 33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_440 v H)
lemma reduced_441 : word v [69, 8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_441 v H)
lemma mul_reduced_441 (x : A) : word v [69, 8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_441 v H)
lemma reduced_442 : word v [3, 40, 60, 4, 54, 16, 58]=word v [3, 40, 60, 4, 54, 15, 1] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_442 v H)
lemma mul_reduced_442 (x : A) : word v [3, 40, 60, 4, 54, 16, 58]*x=(word v [3, 40, 60, 4, 54, 15, 1]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_442 v H)
lemma reduced_443 : word v [37, 24, 19, 53, 54, 15, 1]=word v [37, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_443 v H)
lemma mul_reduced_443 (x : A) : word v [37, 24, 19, 53, 54, 15, 1]*x=(word v [37, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_443 v H)
lemma reduced_444 : word v [66, 24, 19, 53, 54, 15, 1]=word v [66, 24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_444 v H)
lemma mul_reduced_444 (x : A) : word v [66, 24, 19, 53, 54, 15, 1]*x=(word v [66, 24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_444 v H)
lemma reduced_445 : word v [3, 40, 60, 4, 54, 16, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_445 v H)
lemma mul_reduced_445 (x : A) : word v [3, 40, 60, 4, 54, 16, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_445 v H)
lemma reduced_446 : word v [37, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_446 v H)
lemma mul_reduced_446 (x : A) : word v [37, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_446 v H)
lemma reduced_447 : word v [66, 24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_447 v H)
lemma mul_reduced_447 (x : A) : word v [66, 24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_447 v H)
lemma reduced_448 : word v [35, 55, 27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_448 v H)
lemma mul_reduced_448 (x : A) : word v [35, 55, 27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_448 v H)
lemma reduced_449 : word v [52, 41, 43, 47, 7, 17, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_449 v H)
lemma mul_reduced_449 (x : A) : word v [52, 41, 43, 47, 7, 17, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_449 v H)
lemma reduced_450 : word v [21, 69, 8, 66, 24, 19, 52]=word v [21, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_450 v H)
lemma mul_reduced_450 (x : A) : word v [21, 69, 8, 66, 24, 19, 52]*x=(word v [21, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_450 v H)
lemma reduced_451 : word v [36, 70, 23, 66, 24, 18, 9]=word v [36, 70, 22, 3, 40, 62, 52] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_451 v H)
lemma mul_reduced_451 (x : A) : word v [36, 70, 23, 66, 24, 18, 9]*x=(word v [36, 70, 22, 3, 40, 62, 52]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_451 v H)
lemma reduced_452 : word v [49, 69, 8, 66, 24, 19, 52]=word v [49, 69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_452 v H)
lemma mul_reduced_452 (x : A) : word v [49, 69, 8, 66, 24, 19, 52]*x=(word v [49, 69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_452 v H)
lemma reduced_453 : word v [41, 44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_453 v H)
lemma mul_reduced_453 (x : A) : word v [41, 44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_453 v H)
lemma reduced_454 : word v [54, 15, 1, 34, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_454 v H)
lemma mul_reduced_454 (x : A) : word v [54, 15, 1, 34, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_454 v H)
lemma reduced_455 : word v [41, 43, 47, 7, 17, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_455 v H)
lemma mul_reduced_455 (x : A) : word v [41, 43, 47, 7, 17, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_455 v H)
lemma reduced_456 : word v [55, 27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_456 v H)
lemma mul_reduced_456 (x : A) : word v [55, 27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_456 v H)
lemma reduced_457 : word v [6, 7, 17, 21, 70, 22, 3]=word v [6, 7, 17, 21, 69, 8, 68] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_457 v H)
lemma mul_reduced_457 (x : A) : word v [6, 7, 17, 21, 70, 22, 3]*x=(word v [6, 7, 17, 21, 69, 8, 68]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_457 v H)
lemma reduced_458 : word v [47, 7, 17, 21, 70, 22, 3]=word v [47, 7, 17, 21, 69, 8, 68] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_458 v H)
lemma mul_reduced_458 (x : A) : word v [47, 7, 17, 21, 70, 22, 3]*x=(word v [47, 7, 17, 21, 69, 8, 68]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_458 v H)
lemma reduced_459 : word v [58, 34, 63, 21, 70, 22, 3]=(-word v [58, 33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_459 v H)
lemma mul_reduced_459 (x : A) : word v [58, 34, 63, 21, 70, 22, 3]*x=(-(word v [58, 33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_459 v H)
lemma reduced_460 : word v [13, 49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_460 v H)
lemma mul_reduced_460 (x : A) : word v [13, 49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_460 v H)
lemma reduced_461 : word v [17, 21, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_461 v H)
lemma mul_reduced_461 (x : A) : word v [17, 21, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_461 v H)
lemma reduced_462 : word v [63, 21, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_462 v H)
lemma mul_reduced_462 (x : A) : word v [63, 21, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_462 v H)
lemma reduced_463 : word v [13, 49, 69, 8, 66, 25, 62]=word v [13, 49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_463 v H)
lemma mul_reduced_463 (x : A) : word v [13, 49, 69, 8, 66, 25, 62]*x=(word v [13, 49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_463 v H)
lemma reduced_464 : word v [17, 21, 69, 8, 66, 25, 62]=word v [17, 21, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_464 v H)
lemma mul_reduced_464 (x : A) : word v [17, 21, 69, 8, 66, 25, 62]*x=(word v [17, 21, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_464 v H)
lemma reduced_465 : word v [63, 21, 69, 8, 66, 25, 62]=word v [63, 21, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_465 v H)
lemma mul_reduced_465 (x : A) : word v [63, 21, 69, 8, 66, 25, 62]*x=(word v [63, 21, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_465 v H)
lemma reduced_466 : word v [67, 32, 61, 35, 55, 27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_466 v H)
lemma mul_reduced_466 (x : A) : word v [67, 32, 61, 35, 55, 27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_466 v H)
lemma reduced_467 : word v [13, 49, 71, 72, 38, 28, 14]=word v [13, 49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_467 v H)
lemma mul_reduced_467 (x : A) : word v [13, 49, 71, 72, 38, 28, 14]*x=(word v [13, 49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_467 v H)
lemma reduced_468 : word v [64, 36, 71, 72, 38, 28, 14]=(-word v [63, 21, 69, 8, 66, 24, 18]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_468 v H)
lemma mul_reduced_468 (x : A) : word v [64, 36, 71, 72, 38, 28, 14]*x=(-(word v [63, 21, 69, 8, 66, 24, 18]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_468 v H)
lemma reduced_469 : word v [11, 26, 31, 73, 67, 32, 60]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_469 v H)
lemma mul_reduced_469 (x : A) : word v [11, 26, 31, 73, 67, 32, 60]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_469 v H)
lemma reduced_470 : word v [12, 35, 55, 27, 58, 34, 65]=word v [12, 35, 55, 27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_470 v H)
lemma mul_reduced_470 (x : A) : word v [12, 35, 55, 27, 58, 34, 65]*x=(word v [12, 35, 55, 27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_470 v H)
lemma reduced_471 : word v [61, 35, 55, 27, 58, 34, 65]=word v [61, 35, 55, 27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_471 v H)
lemma mul_reduced_471 (x : A) : word v [61, 35, 55, 27, 58, 34, 65]*x=(word v [61, 35, 55, 27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_471 v H)
lemma reduced_472 : word v [31, 73, 67, 32, 61, 35, 54]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_472 v H)
lemma mul_reduced_472 (x : A) : word v [31, 73, 67, 32, 61, 35, 54]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_472 v H)
lemma reduced_473 : word v [41, 43, 48, 51, 64, 36, 69]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_473 v H)
lemma mul_reduced_473 (x : A) : word v [41, 43, 48, 51, 64, 36, 69]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_473 v H)
lemma reduced_474 : word v [55, 27, 58, 34, 63, 21, 69]=(-word v [55, 27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_474 v H)
lemma mul_reduced_474 (x : A) : word v [55, 27, 58, 34, 63, 21, 69]*x=(-(word v [55, 27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_474 v H)
lemma reduced_475 : word v [33, 13, 49, 71, 72, 38, 29]=word v [33, 13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_475 v H)
lemma mul_reduced_475 (x : A) : word v [33, 13, 49, 71, 72, 38, 29]*x=(word v [33, 13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_475 v H)
lemma reduced_476 : word v [51, 64, 36, 71, 72, 38, 29]=(-word v [50, 17, 21, 69, 8, 66, 24]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_476 v H)
lemma mul_reduced_476 (x : A) : word v [51, 64, 36, 71, 72, 38, 29]*x=(-(word v [50, 17, 21, 69, 8, 66, 24]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_476 v H)
lemma reduced_477 : word v [11, 26, 31, 73, 68, 39, 12]=word v [11, 26, 31, 73, 67, 32, 61] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_477 v H)
lemma mul_reduced_477 (x : A) : word v [11, 26, 31, 73, 68, 39, 12]*x=(word v [11, 26, 31, 73, 67, 32, 61]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_477 v H)
lemma reduced_478 : word v [73, 67, 32, 62, 52, 42, 46]=word v [73, 67, 32, 61, 35, 56, 43] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_478 v H)
lemma mul_reduced_478 (x : A) : word v [73, 67, 32, 62, 52, 42, 46]*x=(word v [73, 67, 32, 61, 35, 56, 43]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_478 v H)
lemma reduced_479 : word v [67, 32, 61, 35, 56, 43, 48]=word v [67, 32, 61, 35, 55, 27, 59] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_479 v H)
lemma mul_reduced_479 (x : A) : word v [67, 32, 61, 35, 56, 43, 48]*x=(word v [67, 32, 61, 35, 55, 27, 59]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_479 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_420 : word (a k) [24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_420 (a k) (relation_zero k)
lemma reduced_421 : word (a k) [28, 14, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_421 (a k) (relation_zero k)
lemma reduced_422 : word (a k) [40, 60, 4, 54, 15, 1, 33]=0 := by
  exact Universal.reduced_422 (a k) (relation_zero k)
lemma reduced_423 : word (a k) [18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_423 (a k) (relation_zero k)
lemma reduced_424 : word (a k) [60, 4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.reduced_424 (a k) (relation_zero k)
lemma reduced_425 : word (a k) [7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_425 (a k) (relation_zero k)
lemma reduced_426 : word (a k) [33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_426 (a k) (relation_zero k)
lemma reduced_427 : word (a k) [50, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_427 (a k) (relation_zero k)
lemma reduced_428 : word (a k) [70, 22, 3, 40, 62, 52, 42]=0 := by
  exact Universal.reduced_428 (a k) (relation_zero k)
lemma reduced_429 : word (a k) [69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_429 (a k) (relation_zero k)
lemma reduced_430 : word (a k) [70, 22, 3, 40, 60, 4, 55]=0 := by
  exact Universal.reduced_430 (a k) (relation_zero k)
lemma reduced_431 : word (a k) [8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_431 (a k) (relation_zero k)
lemma reduced_432 : word (a k) [22, 3, 40, 60, 4, 56, 43]=0 := by
  exact Universal.reduced_432 (a k) (relation_zero k)
lemma reduced_433 : word (a k) [72, 37, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_433 (a k) (relation_zero k)
lemma reduced_434 : word (a k) [14, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_434 (a k) (relation_zero k)
lemma reduced_435 : word (a k) [14, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_435 (a k) (relation_zero k)
lemma reduced_436 : word (a k) [18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_436 (a k) (relation_zero k)
lemma reduced_437 : word (a k) [60, 4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.reduced_437 (a k) (relation_zero k)
lemma reduced_438 : word (a k) [6, 7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.reduced_438 (a k) (relation_zero k)
lemma reduced_439 : word (a k) [47, 7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.reduced_439 (a k) (relation_zero k)
lemma reduced_440 : word (a k) [58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_440 (a k) (relation_zero k)
lemma reduced_441 : word (a k) [69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_441 (a k) (relation_zero k)
lemma reduced_442 : word (a k) [3, 40, 60, 4, 54, 16, 58]=word (a k) [3, 40, 60, 4, 54, 15, 1] := by
  exact Universal.reduced_442 (a k) (relation_zero k)
lemma reduced_443 : word (a k) [37, 24, 19, 53, 54, 15, 1]=word (a k) [37, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_443 (a k) (relation_zero k)
lemma reduced_444 : word (a k) [66, 24, 19, 53, 54, 15, 1]=word (a k) [66, 24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_444 (a k) (relation_zero k)
lemma reduced_445 : word (a k) [3, 40, 60, 4, 54, 16, 59]=0 := by
  exact Universal.reduced_445 (a k) (relation_zero k)
lemma reduced_446 : word (a k) [37, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_446 (a k) (relation_zero k)
lemma reduced_447 : word (a k) [66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_447 (a k) (relation_zero k)
lemma reduced_448 : word (a k) [35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_448 (a k) (relation_zero k)
lemma reduced_449 : word (a k) [52, 41, 43, 47, 7, 17, 20]=0 := by
  exact Universal.reduced_449 (a k) (relation_zero k)
lemma reduced_450 : word (a k) [21, 69, 8, 66, 24, 19, 52]=word (a k) [21, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_450 (a k) (relation_zero k)
lemma reduced_451 : word (a k) [36, 70, 23, 66, 24, 18, 9]=word (a k) [36, 70, 22, 3, 40, 62, 52] := by
  exact Universal.reduced_451 (a k) (relation_zero k)
lemma reduced_452 : word (a k) [49, 69, 8, 66, 24, 19, 52]=word (a k) [49, 69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_452 (a k) (relation_zero k)
lemma reduced_453 : word (a k) [41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_453 (a k) (relation_zero k)
lemma reduced_454 : word (a k) [54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.reduced_454 (a k) (relation_zero k)
lemma reduced_455 : word (a k) [41, 43, 47, 7, 17, 21, 71]=0 := by
  exact Universal.reduced_455 (a k) (relation_zero k)
lemma reduced_456 : word (a k) [55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_456 (a k) (relation_zero k)
lemma reduced_457 : word (a k) [6, 7, 17, 21, 70, 22, 3]=word (a k) [6, 7, 17, 21, 69, 8, 68] := by
  exact Universal.reduced_457 (a k) (relation_zero k)
lemma reduced_458 : word (a k) [47, 7, 17, 21, 70, 22, 3]=word (a k) [47, 7, 17, 21, 69, 8, 68] := by
  exact Universal.reduced_458 (a k) (relation_zero k)
lemma reduced_459 : word (a k) [58, 34, 63, 21, 70, 22, 3]=(-word (a k) [58, 33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_459 (a k) (relation_zero k)
lemma reduced_460 : word (a k) [13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_460 (a k) (relation_zero k)
lemma reduced_461 : word (a k) [17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_461 (a k) (relation_zero k)
lemma reduced_462 : word (a k) [63, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_462 (a k) (relation_zero k)
lemma reduced_463 : word (a k) [13, 49, 69, 8, 66, 25, 62]=word (a k) [13, 49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_463 (a k) (relation_zero k)
lemma reduced_464 : word (a k) [17, 21, 69, 8, 66, 25, 62]=word (a k) [17, 21, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_464 (a k) (relation_zero k)
lemma reduced_465 : word (a k) [63, 21, 69, 8, 66, 25, 62]=word (a k) [63, 21, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_465 (a k) (relation_zero k)
lemma reduced_466 : word (a k) [67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.reduced_466 (a k) (relation_zero k)
lemma reduced_467 : word (a k) [13, 49, 71, 72, 38, 28, 14]=word (a k) [13, 49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_467 (a k) (relation_zero k)
lemma reduced_468 : word (a k) [64, 36, 71, 72, 38, 28, 14]=(-word (a k) [63, 21, 69, 8, 66, 24, 18]) := by
  exact Universal.reduced_468 (a k) (relation_zero k)
lemma reduced_469 : word (a k) [11, 26, 31, 73, 67, 32, 60]=0 := by
  exact Universal.reduced_469 (a k) (relation_zero k)
lemma reduced_470 : word (a k) [12, 35, 55, 27, 58, 34, 65]=word (a k) [12, 35, 55, 27, 58, 33, 13] := by
  exact Universal.reduced_470 (a k) (relation_zero k)
lemma reduced_471 : word (a k) [61, 35, 55, 27, 58, 34, 65]=word (a k) [61, 35, 55, 27, 58, 33, 13] := by
  exact Universal.reduced_471 (a k) (relation_zero k)
lemma reduced_472 : word (a k) [31, 73, 67, 32, 61, 35, 54]=0 := by
  exact Universal.reduced_472 (a k) (relation_zero k)
lemma reduced_473 : word (a k) [41, 43, 48, 51, 64, 36, 69]=0 := by
  exact Universal.reduced_473 (a k) (relation_zero k)
lemma reduced_474 : word (a k) [55, 27, 58, 34, 63, 21, 69]=(-word (a k) [55, 27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_474 (a k) (relation_zero k)
lemma reduced_475 : word (a k) [33, 13, 49, 71, 72, 38, 29]=word (a k) [33, 13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_475 (a k) (relation_zero k)
lemma reduced_476 : word (a k) [51, 64, 36, 71, 72, 38, 29]=(-word (a k) [50, 17, 21, 69, 8, 66, 24]) := by
  exact Universal.reduced_476 (a k) (relation_zero k)
lemma reduced_477 : word (a k) [11, 26, 31, 73, 68, 39, 12]=word (a k) [11, 26, 31, 73, 67, 32, 61] := by
  exact Universal.reduced_477 (a k) (relation_zero k)
lemma reduced_478 : word (a k) [73, 67, 32, 62, 52, 42, 46]=word (a k) [73, 67, 32, 61, 35, 56, 43] := by
  exact Universal.reduced_478 (a k) (relation_zero k)
lemma reduced_479 : word (a k) [67, 32, 61, 35, 56, 43, 48]=word (a k) [67, 32, 61, 35, 55, 27, 59] := by
  exact Universal.reduced_479 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
