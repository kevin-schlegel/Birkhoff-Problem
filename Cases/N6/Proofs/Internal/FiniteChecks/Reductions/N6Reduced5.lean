import N6Rules29
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma reduced_300 : word v [46, 48, 51, 65, 49]=(-word v [45, 6, 7, 17, 21]) + word v [46, 48, 51, 64, 36] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_300 v H)
lemma mul_reduced_300 (x : A) : word v [46, 48, 51, 65, 49]*x=(-(word v [45, 6, 7, 17, 21]*x)) + (word v [46, 48, 51, 64, 36]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_300 v H)
lemma reduced_301 : word v [21, 69, 8, 68, 40]=(-word v [21, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_301 v H)
lemma mul_reduced_301 (x : A) : word v [21, 69, 8, 68, 40]*x=(-(word v [21, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_301 v H)
lemma reduced_302 : word v [26, 31, 73, 68, 40]=word v [26, 31, 73, 67, 32] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_302 v H)
lemma mul_reduced_302 (x : A) : word v [26, 31, 73, 68, 40]*x=(word v [26, 31, 73, 67, 32]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_302 v H)
lemma reduced_303 : word v [36, 70, 23, 66, 25]=word v [36, 70, 22, 3, 40] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_303 v H)
lemma mul_reduced_303 (x : A) : word v [36, 70, 23, 66, 25]*x=(word v [36, 70, 22, 3, 40]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_303 v H)
lemma reduced_304 : word v [49, 69, 8, 68, 40]=(-word v [49, 69, 8, 66, 25]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_304 v H)
lemma mul_reduced_304 (x : A) : word v [49, 69, 8, 68, 40]*x=(-(word v [49, 69, 8, 66, 25]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_304 v H)
lemma reduced_305 : word v [7, 17, 21, 70, 23]=(-word v [7, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_305 v H)
lemma mul_reduced_305 (x : A) : word v [7, 17, 21, 70, 23]*x=(-(word v [7, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_305 v H)
lemma reduced_306 : word v [33, 13, 49, 71, 73]=word v [33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_306 v H)
lemma mul_reduced_306 (x : A) : word v [33, 13, 49, 71, 73]*x=(word v [33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_306 v H)
lemma reduced_307 : word v [34, 63, 21, 70, 23]=word v [33, 13, 49, 69, 8] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_307 v H)
lemma mul_reduced_307 (x : A) : word v [34, 63, 21, 70, 23]*x=(word v [33, 13, 49, 69, 8]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_307 v H)
lemma reduced_308 : word v [50, 17, 21, 70, 23]=(-word v [50, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_308 v H)
lemma mul_reduced_308 (x : A) : word v [50, 17, 21, 70, 23]*x=(-(word v [50, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_308 v H)
lemma reduced_309 : word v [51, 64, 36, 71, 73]=(-word v [50, 17, 21, 69, 8]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_309 v H)
lemma mul_reduced_309 (x : A) : word v [51, 64, 36, 71, 73]*x=(-(word v [50, 17, 21, 69, 8]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_309 v H)
lemma reduced_310 : word v [11, 26, 31, 73, 66]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_310 v H)
lemma mul_reduced_310 (x : A) : word v [11, 26, 31, 73, 66]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_310 v H)
lemma reduced_311 : word v [13, 49, 71, 72, 37]=word v [13, 49, 69, 8, 66] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_311 v H)
lemma mul_reduced_311 (x : A) : word v [13, 49, 71, 72, 37]*x=(word v [13, 49, 69, 8, 66]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_311 v H)
lemma reduced_312 : word v [64, 36, 71, 72, 37]=(-word v [63, 21, 69, 8, 66]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_312 v H)
lemma mul_reduced_312 (x : A) : word v [64, 36, 71, 72, 37]*x=(-(word v [63, 21, 69, 8, 66]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_312 v H)
lemma reduced_313 : word v [18, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_313 v H)
lemma mul_reduced_313 (x : A) : word v [18, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_313 v H)
lemma reduced_314 : word v [60, 4, 54, 15, 1, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_314 v H)
lemma mul_reduced_314 (x : A) : word v [60, 4, 54, 15, 1, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_314 v H)
lemma reduced_315 : word v [4, 54, 15, 1, 34, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_315 v H)
lemma mul_reduced_315 (x : A) : word v [4, 54, 15, 1, 34, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_315 v H)
lemma reduced_316 : word v [52, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_316 v H)
lemma mul_reduced_316 (x : A) : word v [52, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_316 v H)
lemma reduced_317 : word v [17, 21, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_317 v H)
lemma mul_reduced_317 (x : A) : word v [17, 21, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_317 v H)
lemma reduced_318 : word v [63, 21, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_318 v H)
lemma mul_reduced_318 (x : A) : word v [63, 21, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_318 v H)
lemma reduced_319 : word v [22, 3, 40, 62, 52, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_319 v H)
lemma mul_reduced_319 (x : A) : word v [22, 3, 40, 62, 52, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_319 v H)
lemma reduced_320 : word v [8, 66, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_320 v H)
lemma mul_reduced_320 (x : A) : word v [8, 66, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_320 v H)
lemma reduced_321 : word v [22, 3, 40, 60, 4, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_321 v H)
lemma mul_reduced_321 (x : A) : word v [22, 3, 40, 60, 4, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_321 v H)
lemma reduced_322 : word v [72, 37, 24, 19, 53, 55]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_322 v H)
lemma mul_reduced_322 (x : A) : word v [72, 37, 24, 19, 53, 55]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_322 v H)
lemma reduced_323 : word v [3, 40, 60, 4, 56, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_323 v H)
lemma mul_reduced_323 (x : A) : word v [3, 40, 60, 4, 56, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_323 v H)
lemma reduced_324 : word v [37, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_324 v H)
lemma mul_reduced_324 (x : A) : word v [37, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_324 v H)
lemma reduced_325 : word v [66, 24, 18, 9, 41, 43]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_325 v H)
lemma mul_reduced_325 (x : A) : word v [66, 24, 18, 9, 41, 43]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_325 v H)
lemma reduced_326 : word v [9, 41, 44, 57, 5, 64]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_326 v H)
lemma mul_reduced_326 (x : A) : word v [9, 41, 44, 57, 5, 64]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_326 v H)
lemma reduced_327 : word v [4, 54, 15, 1, 34, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_327 v H)
lemma mul_reduced_327 (x : A) : word v [4, 54, 15, 1, 34, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_327 v H)
lemma reduced_328 : word v [9, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_328 v H)
lemma mul_reduced_328 (x : A) : word v [9, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_328 v H)
lemma reduced_329 : word v [52, 41, 44, 57, 5, 65]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_329 v H)
lemma mul_reduced_329 (x : A) : word v [52, 41, 44, 57, 5, 65]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_329 v H)
lemma reduced_330 : word v [13, 49, 69, 8, 68, 39]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_330 v H)
lemma mul_reduced_330 (x : A) : word v [13, 49, 69, 8, 68, 39]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_330 v H)
lemma reduced_331 : word v [7, 17, 21, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_331 v H)
lemma mul_reduced_331 (x : A) : word v [7, 17, 21, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_331 v H)
lemma reduced_332 : word v [33, 13, 49, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_332 v H)
lemma mul_reduced_332 (x : A) : word v [33, 13, 49, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_332 v H)
lemma reduced_333 : word v [50, 17, 21, 69, 8, 67]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_333 v H)
lemma mul_reduced_333 (x : A) : word v [50, 17, 21, 69, 8, 67]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_333 v H)
lemma reduced_334 : word v [14, 9, 41, 44, 58, 33]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_334 v H)
lemma mul_reduced_334 (x : A) : word v [14, 9, 41, 44, 58, 33]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_334 v H)
lemma reduced_335 : word v [8, 66, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_335 v H)
lemma mul_reduced_335 (x : A) : word v [8, 66, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_335 v H)
lemma reduced_336 : word v [72, 37, 24, 18, 9, 42]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_336 v H)
lemma mul_reduced_336 (x : A) : word v [72, 37, 24, 18, 9, 42]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_336 v H)
lemma reduced_337 : word v [24, 19, 53, 54, 15, 1]=word v [24, 18, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_337 v H)
lemma mul_reduced_337 (x : A) : word v [24, 19, 53, 54, 15, 1]*x=(word v [24, 18, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_337 v H)
lemma reduced_338 : word v [29, 19, 53, 54, 15, 1]=word v [28, 14, 9, 41, 44, 58] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_338 v H)
lemma mul_reduced_338 (x : A) : word v [29, 19, 53, 54, 15, 1]*x=(word v [28, 14, 9, 41, 44, 58]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_338 v H)
lemma reduced_339 : word v [40, 60, 4, 54, 16, 58]=word v [40, 60, 4, 54, 15, 1] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_339 v H)
lemma mul_reduced_339 (x : A) : word v [40, 60, 4, 54, 16, 58]*x=(word v [40, 60, 4, 54, 15, 1]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_339 v H)
lemma reduced_340 : word v [24, 18, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_340 v H)
lemma mul_reduced_340 (x : A) : word v [24, 18, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_340 v H)
lemma reduced_341 : word v [28, 14, 9, 41, 44, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_341 v H)
lemma mul_reduced_341 (x : A) : word v [28, 14, 9, 41, 44, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_341 v H)
lemma reduced_342 : word v [40, 60, 4, 54, 16, 59]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_342 v H)
lemma mul_reduced_342 (x : A) : word v [40, 60, 4, 54, 16, 59]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_342 v H)
lemma reduced_343 : word v [41, 43, 47, 7, 17, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_343 v H)
lemma mul_reduced_343 (x : A) : word v [41, 43, 47, 7, 17, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_343 v H)
lemma reduced_344 : word v [55, 27, 58, 34, 63, 20]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_344 v H)
lemma mul_reduced_344 (x : A) : word v [55, 27, 58, 34, 63, 20]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_344 v H)
lemma reduced_345 : word v [69, 8, 66, 24, 19, 52]=word v [69, 8, 66, 24, 18, 9] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_345 v H)
lemma mul_reduced_345 (x : A) : word v [69, 8, 66, 24, 19, 52]*x=(word v [69, 8, 66, 24, 18, 9]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_345 v H)
lemma reduced_346 : word v [70, 23, 66, 24, 18, 9]=word v [70, 22, 3, 40, 62, 52] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_346 v H)
lemma mul_reduced_346 (x : A) : word v [70, 23, 66, 24, 18, 9]*x=(word v [70, 22, 3, 40, 62, 52]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_346 v H)
lemma reduced_347 : word v [15, 1, 34, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_347 v H)
lemma mul_reduced_347 (x : A) : word v [15, 1, 34, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_347 v H)
lemma reduced_348 : word v [44, 57, 5, 63, 20, 31]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_348 v H)
lemma mul_reduced_348 (x : A) : word v [44, 57, 5, 63, 20, 31]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_348 v H)
lemma reduced_349 : word v [27, 58, 34, 63, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_349 v H)
lemma mul_reduced_349 (x : A) : word v [27, 58, 34, 63, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_349 v H)
lemma reduced_350 : word v [43, 47, 7, 17, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_350 v H)
lemma mul_reduced_350 (x : A) : word v [43, 47, 7, 17, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_350 v H)
lemma reduced_351 : word v [45, 6, 7, 17, 21, 71]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_351 v H)
lemma mul_reduced_351 (x : A) : word v [45, 6, 7, 17, 21, 71]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_351 v H)
lemma reduced_352 : word v [7, 17, 21, 70, 22, 3]=word v [7, 17, 21, 69, 8, 68] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_352 v H)
lemma mul_reduced_352 (x : A) : word v [7, 17, 21, 70, 22, 3]*x=(word v [7, 17, 21, 69, 8, 68]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_352 v H)
lemma reduced_353 : word v [34, 63, 21, 70, 22, 3]=(-word v [33, 13, 49, 69, 8, 68]) := by
  linear_combination (norm := abel) (1:ℤ) • (rule_353 v H)
lemma mul_reduced_353 (x : A) : word v [34, 63, 21, 70, 22, 3]*x=(-(word v [33, 13, 49, 69, 8, 68]*x)) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_353 v H)
lemma reduced_354 : word v [50, 17, 21, 70, 22, 3]=word v [50, 17, 21, 69, 8, 68] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_354 v H)
lemma mul_reduced_354 (x : A) : word v [50, 17, 21, 70, 22, 3]*x=(word v [50, 17, 21, 69, 8, 68]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_354 v H)
lemma reduced_355 : word v [21, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_355 v H)
lemma mul_reduced_355 (x : A) : word v [21, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_355 v H)
lemma reduced_356 : word v [36, 70, 22, 3, 40, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_356 v H)
lemma mul_reduced_356 (x : A) : word v [36, 70, 22, 3, 40, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_356 v H)
lemma reduced_357 : word v [49, 69, 8, 66, 25, 61]=0 := by
  linear_combination (norm := abel) (1:ℤ) • (rule_357 v H)
lemma mul_reduced_357 (x : A) : word v [49, 69, 8, 66, 25, 61]*x=0 := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_357 v H)
lemma reduced_358 : word v [21, 69, 8, 66, 25, 62]=word v [21, 69, 8, 66, 24, 19] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_358 v H)
lemma mul_reduced_358 (x : A) : word v [21, 69, 8, 66, 25, 62]*x=(word v [21, 69, 8, 66, 24, 19]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_358 v H)
lemma reduced_359 : word v [36, 70, 23, 66, 24, 19]=word v [36, 70, 22, 3, 40, 62] := by
  linear_combination (norm := abel) (1:ℤ) • (rule_359 v H)
lemma mul_reduced_359 (x : A) : word v [36, 70, 23, 66, 24, 19]*x=(word v [36, 70, 22, 3, 40, 62]*x) := by
  simpa only [add_mul,neg_mul,zero_mul,smul_mul_assoc] using congrArg (fun y : A => y*x) (reduced_359 v H)
end UniserialComputations.N6.Presentation.Universal
namespace UniserialComputations.N6.Presentation
variable (k : Type*) [Field k]
lemma reduced_300 : word (a k) [46, 48, 51, 65, 49]=(-word (a k) [45, 6, 7, 17, 21]) + word (a k) [46, 48, 51, 64, 36] := by
  exact Universal.reduced_300 (a k) (relation_zero k)
lemma reduced_301 : word (a k) [21, 69, 8, 68, 40]=(-word (a k) [21, 69, 8, 66, 25]) := by
  exact Universal.reduced_301 (a k) (relation_zero k)
lemma reduced_302 : word (a k) [26, 31, 73, 68, 40]=word (a k) [26, 31, 73, 67, 32] := by
  exact Universal.reduced_302 (a k) (relation_zero k)
lemma reduced_303 : word (a k) [36, 70, 23, 66, 25]=word (a k) [36, 70, 22, 3, 40] := by
  exact Universal.reduced_303 (a k) (relation_zero k)
lemma reduced_304 : word (a k) [49, 69, 8, 68, 40]=(-word (a k) [49, 69, 8, 66, 25]) := by
  exact Universal.reduced_304 (a k) (relation_zero k)
lemma reduced_305 : word (a k) [7, 17, 21, 70, 23]=(-word (a k) [7, 17, 21, 69, 8]) := by
  exact Universal.reduced_305 (a k) (relation_zero k)
lemma reduced_306 : word (a k) [33, 13, 49, 71, 73]=word (a k) [33, 13, 49, 69, 8] := by
  exact Universal.reduced_306 (a k) (relation_zero k)
lemma reduced_307 : word (a k) [34, 63, 21, 70, 23]=word (a k) [33, 13, 49, 69, 8] := by
  exact Universal.reduced_307 (a k) (relation_zero k)
lemma reduced_308 : word (a k) [50, 17, 21, 70, 23]=(-word (a k) [50, 17, 21, 69, 8]) := by
  exact Universal.reduced_308 (a k) (relation_zero k)
lemma reduced_309 : word (a k) [51, 64, 36, 71, 73]=(-word (a k) [50, 17, 21, 69, 8]) := by
  exact Universal.reduced_309 (a k) (relation_zero k)
lemma reduced_310 : word (a k) [11, 26, 31, 73, 66]=0 := by
  exact Universal.reduced_310 (a k) (relation_zero k)
lemma reduced_311 : word (a k) [13, 49, 71, 72, 37]=word (a k) [13, 49, 69, 8, 66] := by
  exact Universal.reduced_311 (a k) (relation_zero k)
lemma reduced_312 : word (a k) [64, 36, 71, 72, 37]=(-word (a k) [63, 21, 69, 8, 66]) := by
  exact Universal.reduced_312 (a k) (relation_zero k)
lemma reduced_313 : word (a k) [18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_313 (a k) (relation_zero k)
lemma reduced_314 : word (a k) [60, 4, 54, 15, 1, 33]=0 := by
  exact Universal.reduced_314 (a k) (relation_zero k)
lemma reduced_315 : word (a k) [4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.reduced_315 (a k) (relation_zero k)
lemma reduced_316 : word (a k) [52, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_316 (a k) (relation_zero k)
lemma reduced_317 : word (a k) [17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_317 (a k) (relation_zero k)
lemma reduced_318 : word (a k) [63, 21, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_318 (a k) (relation_zero k)
lemma reduced_319 : word (a k) [22, 3, 40, 62, 52, 42]=0 := by
  exact Universal.reduced_319 (a k) (relation_zero k)
lemma reduced_320 : word (a k) [8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_320 (a k) (relation_zero k)
lemma reduced_321 : word (a k) [22, 3, 40, 60, 4, 55]=0 := by
  exact Universal.reduced_321 (a k) (relation_zero k)
lemma reduced_322 : word (a k) [72, 37, 24, 19, 53, 55]=0 := by
  exact Universal.reduced_322 (a k) (relation_zero k)
lemma reduced_323 : word (a k) [3, 40, 60, 4, 56, 43]=0 := by
  exact Universal.reduced_323 (a k) (relation_zero k)
lemma reduced_324 : word (a k) [37, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_324 (a k) (relation_zero k)
lemma reduced_325 : word (a k) [66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.reduced_325 (a k) (relation_zero k)
lemma reduced_326 : word (a k) [9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.reduced_326 (a k) (relation_zero k)
lemma reduced_327 : word (a k) [4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.reduced_327 (a k) (relation_zero k)
lemma reduced_328 : word (a k) [9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_328 (a k) (relation_zero k)
lemma reduced_329 : word (a k) [52, 41, 44, 57, 5, 65]=0 := by
  exact Universal.reduced_329 (a k) (relation_zero k)
lemma reduced_330 : word (a k) [13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.reduced_330 (a k) (relation_zero k)
lemma reduced_331 : word (a k) [7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.reduced_331 (a k) (relation_zero k)
lemma reduced_332 : word (a k) [33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.reduced_332 (a k) (relation_zero k)
lemma reduced_333 : word (a k) [50, 17, 21, 69, 8, 67]=0 := by
  exact Universal.reduced_333 (a k) (relation_zero k)
lemma reduced_334 : word (a k) [14, 9, 41, 44, 58, 33]=0 := by
  exact Universal.reduced_334 (a k) (relation_zero k)
lemma reduced_335 : word (a k) [8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_335 (a k) (relation_zero k)
lemma reduced_336 : word (a k) [72, 37, 24, 18, 9, 42]=0 := by
  exact Universal.reduced_336 (a k) (relation_zero k)
lemma reduced_337 : word (a k) [24, 19, 53, 54, 15, 1]=word (a k) [24, 18, 9, 41, 44, 58] := by
  exact Universal.reduced_337 (a k) (relation_zero k)
lemma reduced_338 : word (a k) [29, 19, 53, 54, 15, 1]=word (a k) [28, 14, 9, 41, 44, 58] := by
  exact Universal.reduced_338 (a k) (relation_zero k)
lemma reduced_339 : word (a k) [40, 60, 4, 54, 16, 58]=word (a k) [40, 60, 4, 54, 15, 1] := by
  exact Universal.reduced_339 (a k) (relation_zero k)
lemma reduced_340 : word (a k) [24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_340 (a k) (relation_zero k)
lemma reduced_341 : word (a k) [28, 14, 9, 41, 44, 59]=0 := by
  exact Universal.reduced_341 (a k) (relation_zero k)
lemma reduced_342 : word (a k) [40, 60, 4, 54, 16, 59]=0 := by
  exact Universal.reduced_342 (a k) (relation_zero k)
lemma reduced_343 : word (a k) [41, 43, 47, 7, 17, 20]=0 := by
  exact Universal.reduced_343 (a k) (relation_zero k)
lemma reduced_344 : word (a k) [55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.reduced_344 (a k) (relation_zero k)
lemma reduced_345 : word (a k) [69, 8, 66, 24, 19, 52]=word (a k) [69, 8, 66, 24, 18, 9] := by
  exact Universal.reduced_345 (a k) (relation_zero k)
lemma reduced_346 : word (a k) [70, 23, 66, 24, 18, 9]=word (a k) [70, 22, 3, 40, 62, 52] := by
  exact Universal.reduced_346 (a k) (relation_zero k)
lemma reduced_347 : word (a k) [15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.reduced_347 (a k) (relation_zero k)
lemma reduced_348 : word (a k) [44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.reduced_348 (a k) (relation_zero k)
lemma reduced_349 : word (a k) [27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.reduced_349 (a k) (relation_zero k)
lemma reduced_350 : word (a k) [43, 47, 7, 17, 21, 71]=0 := by
  exact Universal.reduced_350 (a k) (relation_zero k)
lemma reduced_351 : word (a k) [45, 6, 7, 17, 21, 71]=0 := by
  exact Universal.reduced_351 (a k) (relation_zero k)
lemma reduced_352 : word (a k) [7, 17, 21, 70, 22, 3]=word (a k) [7, 17, 21, 69, 8, 68] := by
  exact Universal.reduced_352 (a k) (relation_zero k)
lemma reduced_353 : word (a k) [34, 63, 21, 70, 22, 3]=(-word (a k) [33, 13, 49, 69, 8, 68]) := by
  exact Universal.reduced_353 (a k) (relation_zero k)
lemma reduced_354 : word (a k) [50, 17, 21, 70, 22, 3]=word (a k) [50, 17, 21, 69, 8, 68] := by
  exact Universal.reduced_354 (a k) (relation_zero k)
lemma reduced_355 : word (a k) [21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_355 (a k) (relation_zero k)
lemma reduced_356 : word (a k) [36, 70, 22, 3, 40, 61]=0 := by
  exact Universal.reduced_356 (a k) (relation_zero k)
lemma reduced_357 : word (a k) [49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.reduced_357 (a k) (relation_zero k)
lemma reduced_358 : word (a k) [21, 69, 8, 66, 25, 62]=word (a k) [21, 69, 8, 66, 24, 19] := by
  exact Universal.reduced_358 (a k) (relation_zero k)
lemma reduced_359 : word (a k) [36, 70, 23, 66, 24, 19]=word (a k) [36, 70, 22, 3, 40, 62] := by
  exact Universal.reduced_359 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
