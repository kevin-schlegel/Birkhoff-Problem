import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_360 : word v [49, 69, 8, 66, 25, 62]=word v [49, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_360 v H)
lemma mul_reduced_360 (x : A) : word v [49, 69, 8, 66, 25, 62]*x=(word v [49, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_360 v H)
lemma reduced_361 : word v [32, 61, 35, 55, 27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_361 v H)
lemma mul_reduced_361 (x : A) : word v [32, 61, 35, 55, 27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_361 v H)
lemma reduced_362 : word v [39, 12, 35, 55, 27, 57]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_362 v H)
lemma mul_reduced_362 (x : A) : word v [39, 12, 35, 55, 27, 57]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_362 v H)
lemma reduced_363 : word v [36, 71, 72, 38, 28, 14]=word v [36, 70, 23, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_363 v H)
lemma mul_reduced_363 (x : A) : word v [36, 71, 72, 38, 28, 14]*x=(word v [36, 70, 23, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_363 v H)
lemma reduced_364 : word v [49, 71, 72, 38, 28, 14]=word v [49, 69, 8, 66, 24, 18] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_364 v H)
lemma mul_reduced_364 (x : A) : word v [49, 71, 72, 38, 28, 14]*x=(word v [49, 69, 8, 66, 24, 18]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_364 v H)
lemma reduced_365 : word v [74, 10, 11, 26, 31, 72]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_365 v H)
lemma mul_reduced_365 (x : A) : word v [74, 10, 11, 26, 31, 72]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_365 v H)
lemma reduced_366 : word v [26, 31, 73, 67, 32, 60]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_366 v H)
lemma mul_reduced_366 (x : A) : word v [26, 31, 73, 67, 32, 60]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_366 v H)
lemma reduced_367 : word v [35, 55, 27, 58, 34, 65]=word v [35, 55, 27, 58, 33, 13] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_367 v H)
lemma mul_reduced_367 (x : A) : word v [35, 55, 27, 58, 34, 65]*x=(word v [35, 55, 27, 58, 33, 13]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_367 v H)
lemma reduced_368 : word v [52, 41, 44, 58, 33, 13]=word v [52, 41, 43, 48, 51, 65] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_368 v H)
lemma mul_reduced_368 (x : A) : word v [52, 41, 44, 58, 33, 13]*x=(word v [52, 41, 43, 48, 51, 65]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_368 v H)
lemma reduced_369 : word v [73, 67, 32, 61, 35, 54]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_369 v H)
lemma mul_reduced_369 (x : A) : word v [73, 67, 32, 61, 35, 54]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_369 v H)
lemma reduced_370 : word v [27, 58, 34, 63, 21, 69]=(-word v [27, 58, 33, 13, 49, 69]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_370 v H)
lemma mul_reduced_370 (x : A) : word v [27, 58, 34, 63, 21, 69]*x=(-(word v [27, 58, 33, 13, 49, 69]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_370 v H)
lemma reduced_371 : word v [43, 48, 51, 64, 36, 69]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_371 v H)
lemma mul_reduced_371 (x : A) : word v [43, 48, 51, 64, 36, 69]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_371 v H)
lemma reduced_372 : word v [46, 48, 51, 64, 36, 69]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_372 v H)
lemma mul_reduced_372 (x : A) : word v [46, 48, 51, 64, 36, 69]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_372 v H)
lemma reduced_373 : word v [13, 49, 71, 72, 38, 29]=word v [13, 49, 69, 8, 66, 24] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_373 v H)
lemma mul_reduced_373 (x : A) : word v [13, 49, 71, 72, 38, 29]*x=(word v [13, 49, 69, 8, 66, 24]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_373 v H)
lemma reduced_374 : word v [64, 36, 71, 72, 38, 29]=(-word v [63, 21, 69, 8, 66, 24]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_374 v H)
lemma mul_reduced_374 (x : A) : word v [64, 36, 71, 72, 38, 29]*x=(-(word v [63, 21, 69, 8, 66, 24]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_374 v H)
lemma reduced_375 : word v [26, 31, 73, 68, 39, 12]=word v [26, 31, 73, 67, 32, 61] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_375 v H)
lemma mul_reduced_375 (x : A) : word v [26, 31, 73, 68, 39, 12]*x=(word v [26, 31, 73, 67, 32, 61]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_375 v H)
lemma reduced_376 : word v [67, 32, 62, 52, 42, 46]=word v [67, 32, 61, 35, 56, 43] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_376 v H)
lemma mul_reduced_376 (x : A) : word v [67, 32, 62, 52, 42, 46]*x=(word v [67, 32, 61, 35, 56, 43]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_376 v H)
lemma reduced_377 : word v [32, 61, 35, 56, 43, 48]=word v [32, 61, 35, 55, 27, 59] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_377 v H)
lemma mul_reduced_377 (x : A) : word v [32, 61, 35, 56, 43, 48]*x=(word v [32, 61, 35, 55, 27, 59]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_377 v H)
lemma reduced_378 : word v [39, 12, 35, 56, 43, 48]=word v [39, 12, 35, 55, 27, 59] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_378 v H)
lemma mul_reduced_378 (x : A) : word v [39, 12, 35, 56, 43, 48]*x=(word v [39, 12, 35, 55, 27, 59]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_378 v H)
lemma reduced_379 : word v [32, 62, 52, 42, 45, 6]=word v [32, 61, 35, 56, 43, 47] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_379 v H)
lemma mul_reduced_379 (x : A) : word v [32, 62, 52, 42, 45, 6]*x=(word v [32, 61, 35, 56, 43, 47]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_379 v H)
lemma reduced_380 : word v [40, 62, 52, 42, 45, 6]=word v [39, 12, 35, 56, 43, 47] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_380 v H)
lemma mul_reduced_380 (x : A) : word v [40, 62, 52, 42, 45, 6]*x=(word v [39, 12, 35, 56, 43, 47]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_380 v H)
lemma reduced_381 : word v [12, 35, 56, 43, 47, 7]=word v [12, 35, 55, 27, 59, 50] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_381 v H)
lemma mul_reduced_381 (x : A) : word v [12, 35, 56, 43, 47, 7]*x=(word v [12, 35, 55, 27, 59, 50]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_381 v H)
lemma reduced_382 : word v [61, 35, 56, 43, 47, 7]=word v [61, 35, 55, 27, 59, 50] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_382 v H)
lemma mul_reduced_382 (x : A) : word v [61, 35, 56, 43, 47, 7]*x=(word v [61, 35, 55, 27, 59, 50]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_382 v H)
lemma reduced_383 : word v [27, 58, 33, 13, 49, 70]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_383 v H)
lemma mul_reduced_383 (x : A) : word v [27, 58, 33, 13, 49, 70]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_383 v H)
lemma reduced_384 : word v [43, 48, 51, 64, 36, 70]=word v [43, 47, 7, 17, 21, 70] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_384 v H)
lemma mul_reduced_384 (x : A) : word v [43, 48, 51, 64, 36, 70]*x=(word v [43, 47, 7, 17, 21, 70]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_384 v H)
lemma reduced_385 : word v [46, 48, 51, 64, 36, 70]=word v [45, 6, 7, 17, 21, 70] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_385 v H)
lemma mul_reduced_385 (x : A) : word v [46, 48, 51, 64, 36, 70]*x=(word v [45, 6, 7, 17, 21, 70]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_385 v H)
lemma reduced_386 : word v [35, 55, 27, 59, 50, 17]=word v [35, 55, 27, 58, 34, 63] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_386 v H)
lemma mul_reduced_386 (x : A) : word v [35, 55, 27, 59, 50, 17]*x=(word v [35, 55, 27, 58, 34, 63]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_386 v H)
lemma reduced_387 : word v [52, 41, 43, 48, 51, 63]=word v [52, 41, 43, 47, 7, 17] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_387 v H)
lemma mul_reduced_387 (x : A) : word v [52, 41, 43, 48, 51, 63]*x=(word v [52, 41, 43, 47, 7, 17]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_387 v H)
lemma reduced_388 : word v [8, 66, 24, 19, 53, 56]=word v [8, 66, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_388 v H)
lemma mul_reduced_388 (x : A) : word v [8, 66, 24, 19, 53, 56]*x=(word v [8, 66, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_388 v H)
lemma reduced_389 : word v [22, 3, 40, 62, 52, 41]=word v [22, 3, 40, 60, 4, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_389 v H)
lemma mul_reduced_389 (x : A) : word v [22, 3, 40, 62, 52, 41]*x=(word v [22, 3, 40, 60, 4, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_389 v H)
lemma reduced_390 : word v [72, 37, 24, 19, 53, 56]=word v [72, 37, 24, 18, 9, 41] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_390 v H)
lemma mul_reduced_390 (x : A) : word v [72, 37, 24, 19, 53, 56]*x=(word v [72, 37, 24, 18, 9, 41]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_390 v H)
lemma reduced_391 : word v [73, 67, 32, 62, 52, 41]=word v [73, 67, 32, 61, 35, 56] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_391 v H)
lemma mul_reduced_391 (x : A) : word v [73, 67, 32, 62, 52, 41]*x=(word v [73, 67, 32, 61, 35, 56]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_391 v H)
lemma reduced_392 : word v [3, 40, 60, 4, 56, 44]=word v [3, 40, 60, 4, 54, 16] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_392 v H)
lemma mul_reduced_392 (x : A) : word v [3, 40, 60, 4, 56, 44]*x=(word v [3, 40, 60, 4, 54, 16]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_392 v H)
lemma reduced_393 : word v [37, 24, 19, 53, 54, 16]=word v [37, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_393 v H)
lemma mul_reduced_393 (x : A) : word v [37, 24, 19, 53, 54, 16]*x=(word v [37, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_393 v H)
lemma reduced_394 : word v [66, 24, 19, 53, 54, 16]=word v [66, 24, 18, 9, 41, 44] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_394 v H)
lemma mul_reduced_394 (x : A) : word v [66, 24, 19, 53, 54, 16]*x=(word v [66, 24, 18, 9, 41, 44]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_394 v H)
lemma reduced_395 : word v [67, 32, 61, 35, 56, 44]=word v [67, 32, 61, 35, 55, 27] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_395 v H)
lemma mul_reduced_395 (x : A) : word v [67, 32, 61, 35, 56, 44]*x=(word v [67, 32, 61, 35, 55, 27]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_395 v H)
lemma reduced_396 : word v [12, 35, 55, 27, 59, 51]=word v [12, 35, 55, 27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_396 v H)
lemma mul_reduced_396 (x : A) : word v [12, 35, 55, 27, 59, 51]*x=(word v [12, 35, 55, 27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_396 v H)
lemma reduced_397 : word v [14, 9, 41, 44, 58, 34]=word v [14, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_397 v H)
lemma mul_reduced_397 (x : A) : word v [14, 9, 41, 44, 58, 34]*x=(word v [14, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_397 v H)
lemma reduced_398 : word v [18, 9, 41, 44, 58, 34]=word v [18, 9, 41, 44, 57, 5] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_398 v H)
lemma mul_reduced_398 (x : A) : word v [18, 9, 41, 44, 58, 34]*x=(word v [18, 9, 41, 44, 57, 5]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_398 v H)
lemma reduced_399 : word v [60, 4, 54, 16, 57, 5]=word v [60, 4, 54, 15, 1, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_399 v H)
lemma mul_reduced_399 (x : A) : word v [60, 4, 54, 16, 57, 5]*x=(word v [60, 4, 54, 15, 1, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_399 v H)
lemma reduced_400 : word v [61, 35, 55, 27, 59, 51]=word v [61, 35, 55, 27, 58, 34] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_400 v H)
lemma mul_reduced_400 (x : A) : word v [61, 35, 55, 27, 59, 51]*x=(word v [61, 35, 55, 27, 58, 34]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_400 v H)
lemma reduced_401 : word v [31, 73, 67, 32, 62, 53]=word v [31, 73, 67, 32, 61, 35] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_401 v H)
lemma mul_reduced_401 (x : A) : word v [31, 73, 67, 32, 62, 53]*x=(word v [31, 73, 67, 32, 61, 35]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_401 v H)
lemma reduced_402 : word v [69, 8, 66, 25, 60, 4]=word v [69, 8, 66, 24, 19, 53] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_402 v H)
lemma mul_reduced_402 (x : A) : word v [69, 8, 66, 25, 60, 4]*x=(word v [69, 8, 66, 24, 19, 53]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_402 v H)
lemma reduced_403 : word v [70, 22, 3, 40, 62, 53]=word v [70, 22, 3, 40, 60, 4] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_403 v H)
lemma mul_reduced_403 (x : A) : word v [70, 22, 3, 40, 62, 53]*x=(word v [70, 22, 3, 40, 60, 4]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_403 v H)
lemma reduced_404 : word v [41, 43, 48, 51, 65, 49]=(-word v [41, 43, 47, 7, 17, 21]) + word v [41, 43, 48, 51, 64, 36] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_404 v H)
lemma mul_reduced_404 (x : A) : word v [41, 43, 48, 51, 65, 49]*x=(-(word v [41, 43, 47, 7, 17, 21]*x)) + (word v [41, 43, 48, 51, 64, 36]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_404 v H)
lemma reduced_405 : word v [41, 44, 57, 5, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_405 v H)
lemma mul_reduced_405 (x : A) : word v [41, 44, 57, 5, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_405 v H)
lemma reduced_406 : word v [54, 15, 1, 34, 63, 21]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_406 v H)
lemma mul_reduced_406 (x : A) : word v [54, 15, 1, 34, 63, 21]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_406 v H)
lemma reduced_407 : word v [55, 27, 58, 34, 64, 36]=word v [55, 27, 58, 34, 63, 21] + word v [55, 27, 58, 33, 13, 49] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_407 v H)
lemma mul_reduced_407 (x : A) : word v [55, 27, 58, 34, 64, 36]*x=(word v [55, 27, 58, 34, 63, 21]*x) + (word v [55, 27, 58, 33, 13, 49]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_407 v H)
lemma reduced_408 : word v [11, 26, 31, 73, 68, 40]=word v [11, 26, 31, 73, 67, 32] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_408 v H)
lemma mul_reduced_408 (x : A) : word v [11, 26, 31, 73, 68, 40]*x=(word v [11, 26, 31, 73, 67, 32]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_408 v H)
lemma reduced_409 : word v [13, 49, 69, 8, 68, 40]=(-word v [13, 49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_409 v H)
lemma mul_reduced_409 (x : A) : word v [13, 49, 69, 8, 68, 40]*x=(-(word v [13, 49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_409 v H)
lemma reduced_410 : word v [17, 21, 69, 8, 68, 40]=(-word v [17, 21, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_410 v H)
lemma mul_reduced_410 (x : A) : word v [17, 21, 69, 8, 68, 40]*x=(-(word v [17, 21, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_410 v H)
lemma reduced_411 : word v [63, 21, 69, 8, 68, 40]=(-word v [63, 21, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_411 v H)
lemma mul_reduced_411 (x : A) : word v [63, 21, 69, 8, 68, 40]*x=(-(word v [63, 21, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_411 v H)
lemma reduced_412 : word v [6, 7, 17, 21, 70, 23]=(-word v [6, 7, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_412 v H)
lemma mul_reduced_412 (x : A) : word v [6, 7, 17, 21, 70, 23]*x=(-(word v [6, 7, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_412 v H)
lemma reduced_413 : word v [47, 7, 17, 21, 70, 23]=(-word v [47, 7, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_413 v H)
lemma mul_reduced_413 (x : A) : word v [47, 7, 17, 21, 70, 23]*x=(-(word v [47, 7, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_413 v H)
lemma reduced_414 : word v [48, 51, 64, 36, 71, 73]=(-word v [47, 7, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_414 v H)
lemma mul_reduced_414 (x : A) : word v [48, 51, 64, 36, 71, 73]*x=(-(word v [47, 7, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_414 v H)
lemma reduced_415 : word v [58, 33, 13, 49, 71, 73]=word v [58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_415 v H)
lemma mul_reduced_415 (x : A) : word v [58, 33, 13, 49, 71, 73]*x=(word v [58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_415 v H)
lemma reduced_416 : word v [58, 34, 63, 21, 70, 23]=word v [58, 33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_416 v H)
lemma mul_reduced_416 (x : A) : word v [58, 34, 63, 21, 70, 23]*x=(word v [58, 33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_416 v H)
lemma reduced_417 : word v [10, 11, 26, 31, 73, 66]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_417 v H)
lemma mul_reduced_417 (x : A) : word v [10, 11, 26, 31, 73, 66]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_417 v H)
lemma reduced_418 : word v [33, 13, 49, 71, 72, 37]=word v [33, 13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_418 v H)
lemma mul_reduced_418 (x : A) : word v [33, 13, 49, 71, 72, 37]*x=(word v [33, 13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_418 v H)
lemma reduced_419 : word v [51, 64, 36, 71, 72, 37]=(-word v [50, 17, 21, 69, 8, 66]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_419 v H)
lemma mul_reduced_419 (x : A) : word v [51, 64, 36, 71, 72, 37]*x=(-(word v [50, 17, 21, 69, 8, 66]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_419 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_360 : word (a k) [49, 69, 8, 66, 25, 62]=word (a k) [49, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_360 (a k) (relation_zero k)
lemma reduced_361 : word (a k) [32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.reduced_361 (a k) (relation_zero k)
lemma reduced_362 : word (a k) [39, 12, 35, 55, 27, 57]=0 := by
  exact Universal.reduced_362 (a k) (relation_zero k)
lemma reduced_363 : word (a k) [36, 71, 72, 38, 28, 14]=word (a k) [36, 70, 23, 66, 24, 18] := by
  exact Universal.reduced_363 (a k) (relation_zero k)
lemma reduced_364 : word (a k) [49, 71, 72, 38, 28, 14]=word (a k) [49, 69, 8, 66, 24, 18] := by
  exact Universal.reduced_364 (a k) (relation_zero k)
lemma reduced_365 : word (a k) [74, 10, 11, 26, 31, 72]=0 := by
  exact Universal.reduced_365 (a k) (relation_zero k)
lemma reduced_366 : word (a k) [26, 31, 73, 67, 32, 60]=0 := by
  exact Universal.reduced_366 (a k) (relation_zero k)
lemma reduced_367 : word (a k) [35, 55, 27, 58, 34, 65]=word (a k) [35, 55, 27, 58, 33, 13] := by
  exact Universal.reduced_367 (a k) (relation_zero k)
lemma reduced_368 : word (a k) [52, 41, 44, 58, 33, 13]=word (a k) [52, 41, 43, 48, 51, 65] := by
  exact Universal.reduced_368 (a k) (relation_zero k)
lemma reduced_369 : word (a k) [73, 67, 32, 61, 35, 54]=0 := by
  exact Universal.reduced_369 (a k) (relation_zero k)
lemma reduced_370 : word (a k) [27, 58, 34, 63, 21, 69]=(-word (a k) [27, 58, 33, 13, 49, 69]) := by
  exact Universal.reduced_370 (a k) (relation_zero k)
lemma reduced_371 : word (a k) [43, 48, 51, 64, 36, 69]=0 := by
  exact Universal.reduced_371 (a k) (relation_zero k)
lemma reduced_372 : word (a k) [46, 48, 51, 64, 36, 69]=0 := by
  exact Universal.reduced_372 (a k) (relation_zero k)
lemma reduced_373 : word (a k) [13, 49, 71, 72, 38, 29]=word (a k) [13, 49, 69, 8, 66, 24] := by
  exact Universal.reduced_373 (a k) (relation_zero k)
lemma reduced_374 : word (a k) [64, 36, 71, 72, 38, 29]=(-word (a k) [63, 21, 69, 8, 66, 24]) := by
  exact Universal.reduced_374 (a k) (relation_zero k)
lemma reduced_375 : word (a k) [26, 31, 73, 68, 39, 12]=word (a k) [26, 31, 73, 67, 32, 61] := by
  exact Universal.reduced_375 (a k) (relation_zero k)
lemma reduced_376 : word (a k) [67, 32, 62, 52, 42, 46]=word (a k) [67, 32, 61, 35, 56, 43] := by
  exact Universal.reduced_376 (a k) (relation_zero k)
lemma reduced_377 : word (a k) [32, 61, 35, 56, 43, 48]=word (a k) [32, 61, 35, 55, 27, 59] := by
  exact Universal.reduced_377 (a k) (relation_zero k)
lemma reduced_378 : word (a k) [39, 12, 35, 56, 43, 48]=word (a k) [39, 12, 35, 55, 27, 59] := by
  exact Universal.reduced_378 (a k) (relation_zero k)
lemma reduced_379 : word (a k) [32, 62, 52, 42, 45, 6]=word (a k) [32, 61, 35, 56, 43, 47] := by
  exact Universal.reduced_379 (a k) (relation_zero k)
lemma reduced_380 : word (a k) [40, 62, 52, 42, 45, 6]=word (a k) [39, 12, 35, 56, 43, 47] := by
  exact Universal.reduced_380 (a k) (relation_zero k)
lemma reduced_381 : word (a k) [12, 35, 56, 43, 47, 7]=word (a k) [12, 35, 55, 27, 59, 50] := by
  exact Universal.reduced_381 (a k) (relation_zero k)
lemma reduced_382 : word (a k) [61, 35, 56, 43, 47, 7]=word (a k) [61, 35, 55, 27, 59, 50] := by
  exact Universal.reduced_382 (a k) (relation_zero k)
lemma reduced_383 : word (a k) [27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.reduced_383 (a k) (relation_zero k)
lemma reduced_384 : word (a k) [43, 48, 51, 64, 36, 70]=word (a k) [43, 47, 7, 17, 21, 70] := by
  exact Universal.reduced_384 (a k) (relation_zero k)
lemma reduced_385 : word (a k) [46, 48, 51, 64, 36, 70]=word (a k) [45, 6, 7, 17, 21, 70] := by
  exact Universal.reduced_385 (a k) (relation_zero k)
lemma reduced_386 : word (a k) [35, 55, 27, 59, 50, 17]=word (a k) [35, 55, 27, 58, 34, 63] := by
  exact Universal.reduced_386 (a k) (relation_zero k)
lemma reduced_387 : word (a k) [52, 41, 43, 48, 51, 63]=word (a k) [52, 41, 43, 47, 7, 17] := by
  exact Universal.reduced_387 (a k) (relation_zero k)
lemma reduced_388 : word (a k) [8, 66, 24, 19, 53, 56]=word (a k) [8, 66, 24, 18, 9, 41] := by
  exact Universal.reduced_388 (a k) (relation_zero k)
lemma reduced_389 : word (a k) [22, 3, 40, 62, 52, 41]=word (a k) [22, 3, 40, 60, 4, 56] := by
  exact Universal.reduced_389 (a k) (relation_zero k)
lemma reduced_390 : word (a k) [72, 37, 24, 19, 53, 56]=word (a k) [72, 37, 24, 18, 9, 41] := by
  exact Universal.reduced_390 (a k) (relation_zero k)
lemma reduced_391 : word (a k) [73, 67, 32, 62, 52, 41]=word (a k) [73, 67, 32, 61, 35, 56] := by
  exact Universal.reduced_391 (a k) (relation_zero k)
lemma reduced_392 : word (a k) [3, 40, 60, 4, 56, 44]=word (a k) [3, 40, 60, 4, 54, 16] := by
  exact Universal.reduced_392 (a k) (relation_zero k)
lemma reduced_393 : word (a k) [37, 24, 19, 53, 54, 16]=word (a k) [37, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_393 (a k) (relation_zero k)
lemma reduced_394 : word (a k) [66, 24, 19, 53, 54, 16]=word (a k) [66, 24, 18, 9, 41, 44] := by
  exact Universal.reduced_394 (a k) (relation_zero k)
lemma reduced_395 : word (a k) [67, 32, 61, 35, 56, 44]=word (a k) [67, 32, 61, 35, 55, 27] := by
  exact Universal.reduced_395 (a k) (relation_zero k)
lemma reduced_396 : word (a k) [12, 35, 55, 27, 59, 51]=word (a k) [12, 35, 55, 27, 58, 34] := by
  exact Universal.reduced_396 (a k) (relation_zero k)
lemma reduced_397 : word (a k) [14, 9, 41, 44, 58, 34]=word (a k) [14, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_397 (a k) (relation_zero k)
lemma reduced_398 : word (a k) [18, 9, 41, 44, 58, 34]=word (a k) [18, 9, 41, 44, 57, 5] := by
  exact Universal.reduced_398 (a k) (relation_zero k)
lemma reduced_399 : word (a k) [60, 4, 54, 16, 57, 5]=word (a k) [60, 4, 54, 15, 1, 34] := by
  exact Universal.reduced_399 (a k) (relation_zero k)
lemma reduced_400 : word (a k) [61, 35, 55, 27, 59, 51]=word (a k) [61, 35, 55, 27, 58, 34] := by
  exact Universal.reduced_400 (a k) (relation_zero k)
lemma reduced_401 : word (a k) [31, 73, 67, 32, 62, 53]=word (a k) [31, 73, 67, 32, 61, 35] := by
  exact Universal.reduced_401 (a k) (relation_zero k)
lemma reduced_402 : word (a k) [69, 8, 66, 25, 60, 4]=word (a k) [69, 8, 66, 24, 19, 53] := by
  exact Universal.reduced_402 (a k) (relation_zero k)
lemma reduced_403 : word (a k) [70, 22, 3, 40, 62, 53]=word (a k) [70, 22, 3, 40, 60, 4] := by
  exact Universal.reduced_403 (a k) (relation_zero k)
lemma reduced_404 : word (a k) [41, 43, 48, 51, 65, 49]=(-word (a k) [41, 43, 47, 7, 17, 21]) + word (a k) [41, 43, 48, 51, 64, 36] := by
  exact Universal.reduced_404 (a k) (relation_zero k)
lemma reduced_405 : word (a k) [41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.reduced_405 (a k) (relation_zero k)
lemma reduced_406 : word (a k) [54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.reduced_406 (a k) (relation_zero k)
lemma reduced_407 : word (a k) [55, 27, 58, 34, 64, 36]=word (a k) [55, 27, 58, 34, 63, 21] + word (a k) [55, 27, 58, 33, 13, 49] := by
  exact Universal.reduced_407 (a k) (relation_zero k)
lemma reduced_408 : word (a k) [11, 26, 31, 73, 68, 40]=word (a k) [11, 26, 31, 73, 67, 32] := by
  exact Universal.reduced_408 (a k) (relation_zero k)
lemma reduced_409 : word (a k) [13, 49, 69, 8, 68, 40]=(-word (a k) [13, 49, 69, 8, 66, 25]) := by
  exact Universal.reduced_409 (a k) (relation_zero k)
lemma reduced_410 : word (a k) [17, 21, 69, 8, 68, 40]=(-word (a k) [17, 21, 69, 8, 66, 25]) := by
  exact Universal.reduced_410 (a k) (relation_zero k)
lemma reduced_411 : word (a k) [63, 21, 69, 8, 68, 40]=(-word (a k) [63, 21, 69, 8, 66, 25]) := by
  exact Universal.reduced_411 (a k) (relation_zero k)
lemma reduced_412 : word (a k) [6, 7, 17, 21, 70, 23]=(-word (a k) [6, 7, 17, 21, 69, 8]) := by
  exact Universal.reduced_412 (a k) (relation_zero k)
lemma reduced_413 : word (a k) [47, 7, 17, 21, 70, 23]=(-word (a k) [47, 7, 17, 21, 69, 8]) := by
  exact Universal.reduced_413 (a k) (relation_zero k)
lemma reduced_414 : word (a k) [48, 51, 64, 36, 71, 73]=(-word (a k) [47, 7, 17, 21, 69, 8]) := by
  exact Universal.reduced_414 (a k) (relation_zero k)
lemma reduced_415 : word (a k) [58, 33, 13, 49, 71, 73]=word (a k) [58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_415 (a k) (relation_zero k)
lemma reduced_416 : word (a k) [58, 34, 63, 21, 70, 23]=word (a k) [58, 33, 13, 49, 69, 8] := by
  exact Universal.reduced_416 (a k) (relation_zero k)
lemma reduced_417 : word (a k) [10, 11, 26, 31, 73, 66]=0 := by
  exact Universal.reduced_417 (a k) (relation_zero k)
lemma reduced_418 : word (a k) [33, 13, 49, 71, 72, 37]=word (a k) [33, 13, 49, 69, 8, 66] := by
  exact Universal.reduced_418 (a k) (relation_zero k)
lemma reduced_419 : word (a k) [51, 64, 36, 71, 72, 37]=(-word (a k) [50, 17, 21, 69, 8, 66]) := by
  exact Universal.reduced_419 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
