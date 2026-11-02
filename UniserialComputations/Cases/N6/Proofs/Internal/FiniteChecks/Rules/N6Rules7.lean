import N6Rules6
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_420 : word v [24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_337 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_421 : word v [28, 14, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [29, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_338 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_422 : word v [40, 60, 4, 54, 15, 1, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 60, 4, 54, 15]) (defining_0 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_423 : word v [18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_230 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_398 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_424 : word v [60, 4, 54, 15, 1, 34, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [60, 4, 54, 15]) (defining_1 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_425 : word v [7, 17, 21, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_352 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_426 : word v [33, 13, 49, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [34, 63, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_353 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_427 : word v [50, 17, 21, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_354 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_428 : word v [70, 22, 3, 40, 62, 52, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22]) (defining_3 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_429 : word v [69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_402 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_430 : word v [70, 22, 3, 40, 60, 4, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22, 3, 40, 60]) (defining_4 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_431 : word v [8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_292 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_388 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_432 : word v [22, 3, 40, 60, 4, 56, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [22, 3, 40, 60]) (defining_5 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_433 : word v [72, 37, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_294 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_390 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_434 : word v [14, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [14, 9, 41, 44, 57]) (defining_6 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_435 : word v [14, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [14, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_436 : word v [18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_437 : word v [60, 4, 54, 15, 1, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [60, 4, 54, 16, 57]) (defining_7 v H)
  have h1 := congrArg (fun x : A => word v [65] * x) (rule_399 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_438 : word v [6, 7, 17, 21, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_439 : word v [47, 7, 17, 21, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_440 : word v [58, 33, 13, 49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_441 : word v [69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 24, 18]) (defining_11 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_442 : (-word v [3, 40, 60, 4, 54, 15, 1]) + word v [3, 40, 60, 4, 54, 16, 58]=0 := by
  have h0 := congrArg (fun x : A => x * word v [3, 40, 60, 4, 54]) (defining_12 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_443 : word v [37, 24, 19, 53, 54, 15, 1] + (-word v [37, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_393 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_444 : word v [66, 24, 19, 53, 54, 15, 1] + (-word v [66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_394 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_445 : word v [3, 40, 60, 4, 54, 16, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [3, 40, 60, 4, 54]) (defining_13 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_446 : word v [37, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_393 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_447 : word v [66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_394 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_448 : word v [35, 55, 27, 58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_386 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_449 : word v [52, 41, 43, 47, 7, 17, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7]) (defining_14 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_450 : (-word v [21, 69, 8, 66, 24, 18, 9]) + word v [21, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_451 : word v [36, 70, 23, 66, 24, 18, 9] + (-word v [36, 70, 22, 3, 40, 62, 52])=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 23, 66, 24]) (defining_16 v H)
  have h1 := congrArg (fun x : A => word v [52] * x) (rule_359 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_452 : (-word v [49, 69, 8, 66, 24, 18, 9]) + word v [49, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_453 : word v [41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_454 : word v [54, 15, 1, 34, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [54, 15, 1, 34, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_455 : word v [41, 43, 47, 7, 17, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_456 : word v [55, 27, 58, 34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_457 : word v [6, 7, 17, 21, 70, 22, 3] + (-word v [6, 7, 17, 21, 69, 8, 68])=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_412 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_458 : word v [47, 7, 17, 21, 70, 22, 3] + (-word v [47, 7, 17, 21, 69, 8, 68])=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_413 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_459 : word v [58, 34, 63, 21, 70, 22, 3] + word v [58, 33, 13, 49, 69, 8, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 34, 63, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_416 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_460 : word v [13, 49, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_461 : word v [17, 21, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_462 : word v [63, 21, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_463 : (-word v [13, 49, 69, 8, 66, 24, 19]) + word v [13, 49, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_464 : (-word v [17, 21, 69, 8, 66, 24, 19]) + word v [17, 21, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_465 : (-word v [63, 21, 69, 8, 66, 24, 19]) + word v [63, 21, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_466 : word v [67, 32, 61, 35, 55, 27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55]) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_467 : word v [13, 49, 71, 72, 38, 28, 14] + (-word v [13, 49, 69, 8, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_373 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_468 : word v [64, 36, 71, 72, 38, 28, 14] + word v [63, 21, 69, 8, 66, 24, 18]=0 := by
  have h0 := congrArg (fun x : A => x * word v [64, 36, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_374 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_469 : word v [11, 26, 31, 73, 67, 32, 60]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67]) (defining_27 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_470 : (-word v [12, 35, 55, 27, 58, 33, 13]) + word v [12, 35, 55, 27, 58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_471 : (-word v [61, 35, 55, 27, 58, 33, 13]) + word v [61, 35, 55, 27, 58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_472 : word v [31, 73, 67, 32, 61, 35, 54]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61]) (defining_29 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_473 : word v [41, 43, 48, 51, 64, 36, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 48, 51, 64]) (defining_30 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_474 : word v [55, 27, 58, 34, 63, 21, 69] + word v [55, 27, 58, 33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_407 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_475 : (-word v [33, 13, 49, 69, 8, 66, 24]) + word v [33, 13, 49, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_418 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_476 : word v [50, 17, 21, 69, 8, 66, 24] + word v [51, 64, 36, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [51, 64, 36, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_419 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_477 : word v [11, 26, 31, 73, 68, 39, 12] + (-word v [11, 26, 31, 73, 67, 32, 61])=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 68]) (defining_32 v H)
  have h1 := congrArg (fun x : A => word v [61] * x) (rule_408 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_478 : (-word v [73, 67, 32, 61, 35, 56, 43]) + word v [73, 67, 32, 62, 52, 42, 46]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 62, 52]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [43] * x) (rule_391 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_479 : word v [67, 32, 61, 35, 56, 43, 48] + (-word v [67, 32, 61, 35, 55, 27, 59])=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 56]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_395 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_480 : word v [67, 32, 62, 52, 42, 45, 6] + (-word v [67, 32, 61, 35, 56, 43, 47])=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 62, 52, 42]) (defining_35 v H)
  have h1 := congrArg (fun x : A => word v [47] * x) (rule_376 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_481 : word v [32, 61, 35, 56, 43, 47, 7] + (-word v [32, 61, 35, 55, 27, 59, 50])=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 56, 43]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [50] * x) (rule_377 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_482 : word v [39, 12, 35, 56, 43, 47, 7] + (-word v [39, 12, 35, 55, 27, 59, 50])=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 56, 43]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [50] * x) (rule_378 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_483 : (-word v [41, 43, 47, 7, 17, 21, 70]) + word v [41, 43, 48, 51, 64, 36, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 48, 51, 65]) (defining_37 v H)
  have h1 := congrArg (fun x : A => word v [70] * x) (rule_404 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_484 : word v [55, 27, 58, 33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_485 : word v [12, 35, 55, 27, 59, 50, 17] + (-word v [12, 35, 55, 27, 58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_396 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_486 : word v [61, 35, 55, 27, 59, 50, 17] + (-word v [61, 35, 55, 27, 58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_400 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_487 : word v [31, 73, 67, 32, 62, 52, 41] + (-word v [31, 73, 67, 32, 61, 35, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_401 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_488 : (-word v [69, 8, 66, 24, 18, 9, 41]) + word v [69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_345 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_489 : word v [70, 22, 3, 40, 62, 52, 41] + (-word v [70, 22, 3, 40, 60, 4, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22, 3, 40, 62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_403 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_490 : word v [8, 66, 24, 19, 53, 54, 16] + (-word v [8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_320 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_388 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_491 : (-word v [22, 3, 40, 60, 4, 54, 16]) + word v [22, 3, 40, 60, 4, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [22, 3, 40, 60, 4]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_321 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_492 : word v [72, 37, 24, 19, 53, 54, 16] + (-word v [72, 37, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_322 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_390 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_493 : (-word v [73, 67, 32, 61, 35, 55, 27]) + word v [73, 67, 32, 61, 35, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [16] * x) (rule_369 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_494 : (-word v [24, 18, 9, 41, 44, 57, 5]) + word v [24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_340 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_495 : (-word v [28, 14, 9, 41, 44, 57, 5]) + word v [28, 14, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [28, 14, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_341 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_496 : (-word v [32, 61, 35, 55, 27, 58, 34]) + word v [32, 61, 35, 55, 27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_361 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_497 : (-word v [39, 12, 35, 55, 27, 58, 34]) + word v [39, 12, 35, 55, 27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_362 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_498 : word v [40, 60, 4, 54, 16, 57, 5] + (-word v [40, 60, 4, 54, 15, 1, 34])=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 60, 4, 54, 16]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [34] * x) (rule_339 v H)
  have h2 := congrArg (fun x : A => word v [51] * x) (rule_342 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_499 : word v [21, 69, 8, 66, 25, 60, 4] + (-word v [21, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_355 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_358 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_500 : (-word v [26, 31, 73, 67, 32, 61, 35]) + word v [26, 31, 73, 67, 32, 62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [4] * x) (rule_366 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_501 : (-word v [36, 70, 22, 3, 40, 60, 4]) + word v [36, 70, 22, 3, 40, 62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22, 3, 40]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_356 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_502 : word v [49, 69, 8, 66, 25, 60, 4] + (-word v [49, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_357 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_360 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_503 : word v [4, 54, 15, 1, 34, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [4, 54, 15, 1, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_315 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_327 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_504 : word v [9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_326 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_328 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_505 : (-word v [35, 55, 27, 58, 34, 63, 21]) + word v [35, 55, 27, 58, 34, 64, 36] + (-word v [35, 55, 27, 58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_367 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_506 : word v [52, 41, 43, 47, 7, 17, 21] + (-word v [52, 41, 43, 48, 51, 64, 36]) + word v [52, 41, 43, 48, 51, 65, 49]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 48, 51]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [21] * x) (rule_387 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_507 : word v [52, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_316 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_329 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_508 : word v [7, 17, 21, 69, 8, 66, 25] + word v [7, 17, 21, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_331 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_509 : (-word v [10, 11, 26, 31, 73, 67, 32]) + word v [10, 11, 26, 31, 73, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [25] * x) (rule_417 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_510 : word v [33, 13, 49, 69, 8, 66, 25] + word v [33, 13, 49, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_332 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_511 : word v [50, 17, 21, 69, 8, 66, 25] + word v [50, 17, 21, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_333 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_512 : (-word v [27, 58, 33, 13, 49, 69, 8]) + word v [27, 58, 33, 13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_383 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_513 : (-word v [27, 58, 33, 13, 49, 69, 8]) + word v [27, 58, 34, 63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 34, 63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_370 v H)
  have h2 := congrArg (fun x : A => word v [73] * x) (rule_349 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_514 : word v [43, 47, 7, 17, 21, 69, 8] + word v [43, 47, 7, 17, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [73] * x) (rule_350 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_515 : word v [43, 48, 51, 64, 36, 71, 73] + word v [43, 47, 7, 17, 21, 69, 8]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 48, 51, 64, 36]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_371 v H)
  have h2 := congrArg (fun x : A => word v [23] * x) (rule_384 v H)
  have h3 := congrArg (fun x : A => word v [] * x) (rule_514 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (1) * h2 + (1) * h3
lemma rule_516 : word v [45, 6, 7, 17, 21, 69, 8] + word v [45, 6, 7, 17, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [73] * x) (rule_351 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_517 : word v [46, 48, 51, 64, 36, 71, 73] + word v [45, 6, 7, 17, 21, 69, 8]=0 := by
  have h0 := congrArg (fun x : A => x * word v [46, 48, 51, 64, 36]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_372 v H)
  have h2 := congrArg (fun x : A => word v [23] * x) (rule_385 v H)
  have h3 := congrArg (fun x : A => word v [] * x) (rule_516 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (1) * h2 + (1) * h3
lemma rule_518 : word v [48, 51, 64, 36, 71, 72, 37] + word v [47, 7, 17, 21, 69, 8, 66]=0 := by
  have h0 := congrArg (fun x : A => x * word v [48, 51, 64, 36, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_414 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_519 : word v [58, 33, 13, 49, 71, 72, 37] + (-word v [58, 33, 13, 49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_415 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_520 : word v [74, 10, 11, 26, 31, 73, 66]=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [37] * x) (rule_365 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_420 : word (a k) [24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_420 (a k) (relation_zero k)
lemma rule_421 : word (a k) [28, 14, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_421 (a k) (relation_zero k)
lemma rule_422 : word (a k) [40, 60, 4, 54, 15, 1, 33]=0 := by
  exact Universal.rule_422 (a k) (relation_zero k)
lemma rule_423 : word (a k) [18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_423 (a k) (relation_zero k)
lemma rule_424 : word (a k) [60, 4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.rule_424 (a k) (relation_zero k)
lemma rule_425 : word (a k) [7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.rule_425 (a k) (relation_zero k)
lemma rule_426 : word (a k) [33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.rule_426 (a k) (relation_zero k)
lemma rule_427 : word (a k) [50, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.rule_427 (a k) (relation_zero k)
lemma rule_428 : word (a k) [70, 22, 3, 40, 62, 52, 42]=0 := by
  exact Universal.rule_428 (a k) (relation_zero k)
lemma rule_429 : word (a k) [69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_429 (a k) (relation_zero k)
lemma rule_430 : word (a k) [70, 22, 3, 40, 60, 4, 55]=0 := by
  exact Universal.rule_430 (a k) (relation_zero k)
lemma rule_431 : word (a k) [8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_431 (a k) (relation_zero k)
lemma rule_432 : word (a k) [22, 3, 40, 60, 4, 56, 43]=0 := by
  exact Universal.rule_432 (a k) (relation_zero k)
lemma rule_433 : word (a k) [72, 37, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_433 (a k) (relation_zero k)
lemma rule_434 : word (a k) [14, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_434 (a k) (relation_zero k)
lemma rule_435 : word (a k) [14, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_435 (a k) (relation_zero k)
lemma rule_436 : word (a k) [18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_436 (a k) (relation_zero k)
lemma rule_437 : word (a k) [60, 4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.rule_437 (a k) (relation_zero k)
lemma rule_438 : word (a k) [6, 7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.rule_438 (a k) (relation_zero k)
lemma rule_439 : word (a k) [47, 7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.rule_439 (a k) (relation_zero k)
lemma rule_440 : word (a k) [58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.rule_440 (a k) (relation_zero k)
lemma rule_441 : word (a k) [69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_441 (a k) (relation_zero k)
lemma rule_442 : (-word (a k) [3, 40, 60, 4, 54, 15, 1]) + word (a k) [3, 40, 60, 4, 54, 16, 58]=0 := by
  exact Universal.rule_442 (a k) (relation_zero k)
lemma rule_443 : word (a k) [37, 24, 19, 53, 54, 15, 1] + (-word (a k) [37, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_443 (a k) (relation_zero k)
lemma rule_444 : word (a k) [66, 24, 19, 53, 54, 15, 1] + (-word (a k) [66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_444 (a k) (relation_zero k)
lemma rule_445 : word (a k) [3, 40, 60, 4, 54, 16, 59]=0 := by
  exact Universal.rule_445 (a k) (relation_zero k)
lemma rule_446 : word (a k) [37, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_446 (a k) (relation_zero k)
lemma rule_447 : word (a k) [66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_447 (a k) (relation_zero k)
lemma rule_448 : word (a k) [35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.rule_448 (a k) (relation_zero k)
lemma rule_449 : word (a k) [52, 41, 43, 47, 7, 17, 20]=0 := by
  exact Universal.rule_449 (a k) (relation_zero k)
lemma rule_450 : (-word (a k) [21, 69, 8, 66, 24, 18, 9]) + word (a k) [21, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_450 (a k) (relation_zero k)
lemma rule_451 : word (a k) [36, 70, 23, 66, 24, 18, 9] + (-word (a k) [36, 70, 22, 3, 40, 62, 52])=0 := by
  exact Universal.rule_451 (a k) (relation_zero k)
lemma rule_452 : (-word (a k) [49, 69, 8, 66, 24, 18, 9]) + word (a k) [49, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_452 (a k) (relation_zero k)
lemma rule_453 : word (a k) [41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_453 (a k) (relation_zero k)
lemma rule_454 : word (a k) [54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.rule_454 (a k) (relation_zero k)
lemma rule_455 : word (a k) [41, 43, 47, 7, 17, 21, 71]=0 := by
  exact Universal.rule_455 (a k) (relation_zero k)
lemma rule_456 : word (a k) [55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.rule_456 (a k) (relation_zero k)
lemma rule_457 : word (a k) [6, 7, 17, 21, 70, 22, 3] + (-word (a k) [6, 7, 17, 21, 69, 8, 68])=0 := by
  exact Universal.rule_457 (a k) (relation_zero k)
lemma rule_458 : word (a k) [47, 7, 17, 21, 70, 22, 3] + (-word (a k) [47, 7, 17, 21, 69, 8, 68])=0 := by
  exact Universal.rule_458 (a k) (relation_zero k)
lemma rule_459 : word (a k) [58, 34, 63, 21, 70, 22, 3] + word (a k) [58, 33, 13, 49, 69, 8, 68]=0 := by
  exact Universal.rule_459 (a k) (relation_zero k)
lemma rule_460 : word (a k) [13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_460 (a k) (relation_zero k)
lemma rule_461 : word (a k) [17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_461 (a k) (relation_zero k)
lemma rule_462 : word (a k) [63, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_462 (a k) (relation_zero k)
lemma rule_463 : (-word (a k) [13, 49, 69, 8, 66, 24, 19]) + word (a k) [13, 49, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_463 (a k) (relation_zero k)
lemma rule_464 : (-word (a k) [17, 21, 69, 8, 66, 24, 19]) + word (a k) [17, 21, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_464 (a k) (relation_zero k)
lemma rule_465 : (-word (a k) [63, 21, 69, 8, 66, 24, 19]) + word (a k) [63, 21, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_465 (a k) (relation_zero k)
lemma rule_466 : word (a k) [67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.rule_466 (a k) (relation_zero k)
lemma rule_467 : word (a k) [13, 49, 71, 72, 38, 28, 14] + (-word (a k) [13, 49, 69, 8, 66, 24, 18])=0 := by
  exact Universal.rule_467 (a k) (relation_zero k)
lemma rule_468 : word (a k) [64, 36, 71, 72, 38, 28, 14] + word (a k) [63, 21, 69, 8, 66, 24, 18]=0 := by
  exact Universal.rule_468 (a k) (relation_zero k)
lemma rule_469 : word (a k) [11, 26, 31, 73, 67, 32, 60]=0 := by
  exact Universal.rule_469 (a k) (relation_zero k)
lemma rule_470 : (-word (a k) [12, 35, 55, 27, 58, 33, 13]) + word (a k) [12, 35, 55, 27, 58, 34, 65]=0 := by
  exact Universal.rule_470 (a k) (relation_zero k)
lemma rule_471 : (-word (a k) [61, 35, 55, 27, 58, 33, 13]) + word (a k) [61, 35, 55, 27, 58, 34, 65]=0 := by
  exact Universal.rule_471 (a k) (relation_zero k)
lemma rule_472 : word (a k) [31, 73, 67, 32, 61, 35, 54]=0 := by
  exact Universal.rule_472 (a k) (relation_zero k)
lemma rule_473 : word (a k) [41, 43, 48, 51, 64, 36, 69]=0 := by
  exact Universal.rule_473 (a k) (relation_zero k)
lemma rule_474 : word (a k) [55, 27, 58, 34, 63, 21, 69] + word (a k) [55, 27, 58, 33, 13, 49, 69]=0 := by
  exact Universal.rule_474 (a k) (relation_zero k)
lemma rule_475 : (-word (a k) [33, 13, 49, 69, 8, 66, 24]) + word (a k) [33, 13, 49, 71, 72, 38, 29]=0 := by
  exact Universal.rule_475 (a k) (relation_zero k)
lemma rule_476 : word (a k) [50, 17, 21, 69, 8, 66, 24] + word (a k) [51, 64, 36, 71, 72, 38, 29]=0 := by
  exact Universal.rule_476 (a k) (relation_zero k)
lemma rule_477 : word (a k) [11, 26, 31, 73, 68, 39, 12] + (-word (a k) [11, 26, 31, 73, 67, 32, 61])=0 := by
  exact Universal.rule_477 (a k) (relation_zero k)
lemma rule_478 : (-word (a k) [73, 67, 32, 61, 35, 56, 43]) + word (a k) [73, 67, 32, 62, 52, 42, 46]=0 := by
  exact Universal.rule_478 (a k) (relation_zero k)
lemma rule_479 : word (a k) [67, 32, 61, 35, 56, 43, 48] + (-word (a k) [67, 32, 61, 35, 55, 27, 59])=0 := by
  exact Universal.rule_479 (a k) (relation_zero k)
lemma rule_480 : word (a k) [67, 32, 62, 52, 42, 45, 6] + (-word (a k) [67, 32, 61, 35, 56, 43, 47])=0 := by
  exact Universal.rule_480 (a k) (relation_zero k)
lemma rule_481 : word (a k) [32, 61, 35, 56, 43, 47, 7] + (-word (a k) [32, 61, 35, 55, 27, 59, 50])=0 := by
  exact Universal.rule_481 (a k) (relation_zero k)
lemma rule_482 : word (a k) [39, 12, 35, 56, 43, 47, 7] + (-word (a k) [39, 12, 35, 55, 27, 59, 50])=0 := by
  exact Universal.rule_482 (a k) (relation_zero k)
lemma rule_483 : (-word (a k) [41, 43, 47, 7, 17, 21, 70]) + word (a k) [41, 43, 48, 51, 64, 36, 70]=0 := by
  exact Universal.rule_483 (a k) (relation_zero k)
lemma rule_484 : word (a k) [55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.rule_484 (a k) (relation_zero k)
lemma rule_485 : word (a k) [12, 35, 55, 27, 59, 50, 17] + (-word (a k) [12, 35, 55, 27, 58, 34, 63])=0 := by
  exact Universal.rule_485 (a k) (relation_zero k)
lemma rule_486 : word (a k) [61, 35, 55, 27, 59, 50, 17] + (-word (a k) [61, 35, 55, 27, 58, 34, 63])=0 := by
  exact Universal.rule_486 (a k) (relation_zero k)
lemma rule_487 : word (a k) [31, 73, 67, 32, 62, 52, 41] + (-word (a k) [31, 73, 67, 32, 61, 35, 56])=0 := by
  exact Universal.rule_487 (a k) (relation_zero k)
lemma rule_488 : (-word (a k) [69, 8, 66, 24, 18, 9, 41]) + word (a k) [69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_488 (a k) (relation_zero k)
lemma rule_489 : word (a k) [70, 22, 3, 40, 62, 52, 41] + (-word (a k) [70, 22, 3, 40, 60, 4, 56])=0 := by
  exact Universal.rule_489 (a k) (relation_zero k)
lemma rule_490 : word (a k) [8, 66, 24, 19, 53, 54, 16] + (-word (a k) [8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_490 (a k) (relation_zero k)
lemma rule_491 : (-word (a k) [22, 3, 40, 60, 4, 54, 16]) + word (a k) [22, 3, 40, 60, 4, 56, 44]=0 := by
  exact Universal.rule_491 (a k) (relation_zero k)
lemma rule_492 : word (a k) [72, 37, 24, 19, 53, 54, 16] + (-word (a k) [72, 37, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_492 (a k) (relation_zero k)
lemma rule_493 : (-word (a k) [73, 67, 32, 61, 35, 55, 27]) + word (a k) [73, 67, 32, 61, 35, 56, 44]=0 := by
  exact Universal.rule_493 (a k) (relation_zero k)
lemma rule_494 : (-word (a k) [24, 18, 9, 41, 44, 57, 5]) + word (a k) [24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_494 (a k) (relation_zero k)
lemma rule_495 : (-word (a k) [28, 14, 9, 41, 44, 57, 5]) + word (a k) [28, 14, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_495 (a k) (relation_zero k)
lemma rule_496 : (-word (a k) [32, 61, 35, 55, 27, 58, 34]) + word (a k) [32, 61, 35, 55, 27, 59, 51]=0 := by
  exact Universal.rule_496 (a k) (relation_zero k)
lemma rule_497 : (-word (a k) [39, 12, 35, 55, 27, 58, 34]) + word (a k) [39, 12, 35, 55, 27, 59, 51]=0 := by
  exact Universal.rule_497 (a k) (relation_zero k)
lemma rule_498 : word (a k) [40, 60, 4, 54, 16, 57, 5] + (-word (a k) [40, 60, 4, 54, 15, 1, 34])=0 := by
  exact Universal.rule_498 (a k) (relation_zero k)
lemma rule_499 : word (a k) [21, 69, 8, 66, 25, 60, 4] + (-word (a k) [21, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_499 (a k) (relation_zero k)
lemma rule_500 : (-word (a k) [26, 31, 73, 67, 32, 61, 35]) + word (a k) [26, 31, 73, 67, 32, 62, 53]=0 := by
  exact Universal.rule_500 (a k) (relation_zero k)
lemma rule_501 : (-word (a k) [36, 70, 22, 3, 40, 60, 4]) + word (a k) [36, 70, 22, 3, 40, 62, 53]=0 := by
  exact Universal.rule_501 (a k) (relation_zero k)
lemma rule_502 : word (a k) [49, 69, 8, 66, 25, 60, 4] + (-word (a k) [49, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_502 (a k) (relation_zero k)
lemma rule_503 : word (a k) [4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.rule_503 (a k) (relation_zero k)
lemma rule_504 : word (a k) [9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_504 (a k) (relation_zero k)
lemma rule_505 : (-word (a k) [35, 55, 27, 58, 34, 63, 21]) + word (a k) [35, 55, 27, 58, 34, 64, 36] + (-word (a k) [35, 55, 27, 58, 33, 13, 49])=0 := by
  exact Universal.rule_505 (a k) (relation_zero k)
lemma rule_506 : word (a k) [52, 41, 43, 47, 7, 17, 21] + (-word (a k) [52, 41, 43, 48, 51, 64, 36]) + word (a k) [52, 41, 43, 48, 51, 65, 49]=0 := by
  exact Universal.rule_506 (a k) (relation_zero k)
lemma rule_507 : word (a k) [52, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_507 (a k) (relation_zero k)
lemma rule_508 : word (a k) [7, 17, 21, 69, 8, 66, 25] + word (a k) [7, 17, 21, 69, 8, 68, 40]=0 := by
  exact Universal.rule_508 (a k) (relation_zero k)
lemma rule_509 : (-word (a k) [10, 11, 26, 31, 73, 67, 32]) + word (a k) [10, 11, 26, 31, 73, 68, 40]=0 := by
  exact Universal.rule_509 (a k) (relation_zero k)
lemma rule_510 : word (a k) [33, 13, 49, 69, 8, 66, 25] + word (a k) [33, 13, 49, 69, 8, 68, 40]=0 := by
  exact Universal.rule_510 (a k) (relation_zero k)
lemma rule_511 : word (a k) [50, 17, 21, 69, 8, 66, 25] + word (a k) [50, 17, 21, 69, 8, 68, 40]=0 := by
  exact Universal.rule_511 (a k) (relation_zero k)
lemma rule_512 : (-word (a k) [27, 58, 33, 13, 49, 69, 8]) + word (a k) [27, 58, 33, 13, 49, 71, 73]=0 := by
  exact Universal.rule_512 (a k) (relation_zero k)
lemma rule_513 : (-word (a k) [27, 58, 33, 13, 49, 69, 8]) + word (a k) [27, 58, 34, 63, 21, 70, 23]=0 := by
  exact Universal.rule_513 (a k) (relation_zero k)
lemma rule_514 : word (a k) [43, 47, 7, 17, 21, 69, 8] + word (a k) [43, 47, 7, 17, 21, 70, 23]=0 := by
  exact Universal.rule_514 (a k) (relation_zero k)
lemma rule_515 : word (a k) [43, 48, 51, 64, 36, 71, 73] + word (a k) [43, 47, 7, 17, 21, 69, 8]=0 := by
  exact Universal.rule_515 (a k) (relation_zero k)
lemma rule_516 : word (a k) [45, 6, 7, 17, 21, 69, 8] + word (a k) [45, 6, 7, 17, 21, 70, 23]=0 := by
  exact Universal.rule_516 (a k) (relation_zero k)
lemma rule_517 : word (a k) [46, 48, 51, 64, 36, 71, 73] + word (a k) [45, 6, 7, 17, 21, 69, 8]=0 := by
  exact Universal.rule_517 (a k) (relation_zero k)
lemma rule_518 : word (a k) [48, 51, 64, 36, 71, 72, 37] + word (a k) [47, 7, 17, 21, 69, 8, 66]=0 := by
  exact Universal.rule_518 (a k) (relation_zero k)
lemma rule_519 : word (a k) [58, 33, 13, 49, 71, 72, 37] + (-word (a k) [58, 33, 13, 49, 69, 8, 66])=0 := by
  exact Universal.rule_519 (a k) (relation_zero k)
lemma rule_520 : word (a k) [74, 10, 11, 26, 31, 73, 66]=0 := by
  exact Universal.rule_520 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
