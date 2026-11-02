import N6Rules7
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_521 : word v [3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [3, 40, 60, 4, 54, 15]) (defining_0 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_522 : word v [37, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_443 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_523 : word v [66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_444 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_524 : word v [24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_337 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_494 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_525 : word v [28, 14, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [29, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_338 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_495 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_526 : word v [40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 60, 4, 54, 15]) (defining_1 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_527 : word v [6, 7, 17, 21, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_457 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_528 : word v [47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_458 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_529 : word v [58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 34, 63, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_459 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_530 : word v [21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_144 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_301 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_358 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_450 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_531 : word v [36, 70, 22, 3, 40, 62, 52, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22]) (defining_3 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_532 : word v [21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_499 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_533 : word v [36, 70, 22, 3, 40, 60, 4, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22, 3, 40, 60]) (defining_4 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_534 : word v [49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_502 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_535 : word v [69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_402 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_488 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_536 : word v [70, 22, 3, 40, 60, 4, 56, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22, 3, 40, 60]) (defining_5 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_537 : word v [24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_538 : word v [28, 14, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [28, 14, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_539 : word v [40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 60, 4, 54, 16, 57]) (defining_7 v H)
  have h1 := congrArg (fun x : A => word v [65] * x) (rule_498 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_540 : word v [27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_541 : word v [43, 47, 7, 17, 21, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_542 : word v [45, 6, 7, 17, 21, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_543 : word v [49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 24, 18]) (defining_11 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_544 : word v [8, 66, 24, 19, 53, 54, 15, 1] + (-word v [8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_490 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_545 : (-word v [22, 3, 40, 60, 4, 54, 15, 1]) + word v [22, 3, 40, 60, 4, 54, 16, 58]=0 := by
  have h0 := congrArg (fun x : A => x * word v [22, 3, 40, 60, 4, 54]) (defining_12 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_546 : word v [72, 37, 24, 19, 53, 54, 15, 1] + (-word v [72, 37, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_492 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_547 : word v [8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_490 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_548 : word v [22, 3, 40, 60, 4, 54, 16, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [22, 3, 40, 60, 4, 54]) (defining_13 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_549 : word v [72, 37, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_492 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_550 : word v [12, 35, 55, 27, 58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_485 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_551 : word v [61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_486 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_552 : (-word v [13, 49, 69, 8, 66, 24, 18, 9]) + word v [13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_553 : (-word v [17, 21, 69, 8, 66, 24, 18, 9]) + word v [17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_554 : (-word v [63, 21, 69, 8, 66, 24, 18, 9]) + word v [63, 21, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_555 : word v [4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [4, 54, 15, 1, 34, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_556 : word v [9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_557 : word v [52, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_558 : word v [35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_559 : word v [52, 41, 43, 47, 7, 17, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_560 : word v [27, 58, 34, 63, 21, 70, 22, 3] + word v [27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 34, 63, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_513 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_561 : word v [43, 47, 7, 17, 21, 70, 22, 3] + (-word v [43, 47, 7, 17, 21, 69, 8, 68])=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_514 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_562 : word v [45, 6, 7, 17, 21, 70, 22, 3] + (-word v [45, 6, 7, 17, 21, 69, 8, 68])=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_516 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_563 : word v [7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_564 : word v [33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_565 : word v [50, 17, 21, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_566 : (-word v [7, 17, 21, 69, 8, 66, 24, 19]) + word v [7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_567 : (-word v [33, 13, 49, 69, 8, 66, 24, 19]) + word v [33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_568 : (-word v [50, 17, 21, 69, 8, 66, 24, 19]) + word v [50, 17, 21, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_569 : word v [73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55]) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_570 : word v [33, 13, 49, 71, 72, 38, 28, 14] + (-word v [33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_475 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_571 : word v [51, 64, 36, 71, 72, 38, 28, 14] + word v [50, 17, 21, 69, 8, 66, 24, 18]=0 := by
  have h0 := congrArg (fun x : A => x * word v [51, 64, 36, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_476 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_572 : word v [10, 11, 26, 31, 73, 67, 32, 60]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67]) (defining_27 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_573 : (-word v [32, 61, 35, 55, 27, 58, 33, 13]) + word v [32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_574 : (-word v [39, 12, 35, 55, 27, 58, 33, 13]) + word v [39, 12, 35, 55, 27, 58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_575 : word v [26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61]) (defining_29 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_576 : word v [35, 55, 27, 58, 34, 63, 21, 69] + word v [35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_505 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_577 : word v [52, 41, 43, 48, 51, 64, 36, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 48, 51, 64]) (defining_30 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_578 : word v [47, 7, 17, 21, 69, 8, 66, 24] + word v [48, 51, 64, 36, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [48, 51, 64, 36, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_518 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_579 : (-word v [58, 33, 13, 49, 69, 8, 66, 24]) + word v [58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_519 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_580 : word v [10, 11, 26, 31, 73, 68, 39, 12] + (-word v [10, 11, 26, 31, 73, 67, 32, 61])=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 68]) (defining_32 v H)
  have h1 := congrArg (fun x : A => word v [61] * x) (rule_509 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_581 : (-word v [31, 73, 67, 32, 61, 35, 56, 43]) + word v [31, 73, 67, 32, 62, 52, 42, 46]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 62, 52]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [43] * x) (rule_487 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_582 : word v [73, 67, 32, 61, 35, 56, 43, 48] + (-word v [73, 67, 32, 61, 35, 55, 27, 59])=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 56]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_493 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_583 : word v [73, 67, 32, 62, 52, 42, 45, 6] + (-word v [73, 67, 32, 61, 35, 56, 43, 47])=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 62, 52, 42]) (defining_35 v H)
  have h1 := congrArg (fun x : A => word v [47] * x) (rule_478 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_584 : word v [67, 32, 61, 35, 56, 43, 47, 7] + (-word v [67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 56, 43]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [50] * x) (rule_479 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_585 : word v [35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_586 : (-word v [52, 41, 43, 47, 7, 17, 21, 70]) + word v [52, 41, 43, 48, 51, 64, 36, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 48, 51, 65]) (defining_37 v H)
  have h1 := congrArg (fun x : A => word v [70] * x) (rule_506 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_587 : word v [32, 61, 35, 55, 27, 59, 50, 17] + (-word v [32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_496 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_588 : word v [39, 12, 35, 55, 27, 59, 50, 17] + (-word v [39, 12, 35, 55, 27, 58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_497 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_589 : (-word v [21, 69, 8, 66, 24, 18, 9, 41]) + word v [21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_450 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_590 : word v [26, 31, 73, 67, 32, 62, 52, 41] + (-word v [26, 31, 73, 67, 32, 61, 35, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_500 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_591 : word v [36, 70, 22, 3, 40, 62, 52, 41] + (-word v [36, 70, 22, 3, 40, 60, 4, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22, 3, 40, 62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_501 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_592 : (-word v [49, 69, 8, 66, 24, 18, 9, 41]) + word v [49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_452 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_593 : (-word v [31, 73, 67, 32, 61, 35, 55, 27]) + word v [31, 73, 67, 32, 61, 35, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [16] * x) (rule_472 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_594 : word v [69, 8, 66, 24, 19, 53, 54, 16] + (-word v [69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_429 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_488 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_595 : (-word v [70, 22, 3, 40, 60, 4, 54, 16]) + word v [70, 22, 3, 40, 60, 4, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22, 3, 40, 60, 4]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_430 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_596 : word v [3, 40, 60, 4, 54, 16, 57, 5] + (-word v [3, 40, 60, 4, 54, 15, 1, 34])=0 := by
  have h0 := congrArg (fun x : A => x * word v [3, 40, 60, 4, 54, 16]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [34] * x) (rule_442 v H)
  have h2 := congrArg (fun x : A => word v [51] * x) (rule_445 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_597 : (-word v [37, 24, 18, 9, 41, 44, 57, 5]) + word v [37, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_446 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_598 : (-word v [66, 24, 18, 9, 41, 44, 57, 5]) + word v [66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_447 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_599 : (-word v [67, 32, 61, 35, 55, 27, 58, 34]) + word v [67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_466 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_600 : (-word v [11, 26, 31, 73, 67, 32, 61, 35]) + word v [11, 26, 31, 73, 67, 32, 62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [4] * x) (rule_469 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_601 : word v [13, 49, 69, 8, 66, 25, 60, 4] + (-word v [13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_460 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_463 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_602 : word v [17, 21, 69, 8, 66, 25, 60, 4] + (-word v [17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_461 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_464 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_603 : word v [63, 21, 69, 8, 66, 25, 60, 4] + (-word v [63, 21, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_462 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_465 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_604 : (-word v [12, 35, 55, 27, 58, 34, 63, 21]) + word v [12, 35, 55, 27, 58, 34, 64, 36] + (-word v [12, 35, 55, 27, 58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_470 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_605 : word v [14, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [14, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_434 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_435 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_606 : word v [18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_423 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_436 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_607 : word v [60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [60, 4, 54, 15, 1, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_424 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_437 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_608 : (-word v [61, 35, 55, 27, 58, 34, 63, 21]) + word v [61, 35, 55, 27, 58, 34, 64, 36] + (-word v [61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_471 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_609 : word v [6, 7, 17, 21, 69, 8, 66, 25] + word v [6, 7, 17, 21, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_438 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_610 : word v [47, 7, 17, 21, 69, 8, 66, 25] + word v [47, 7, 17, 21, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_439 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_611 : word v [58, 33, 13, 49, 69, 8, 66, 25] + word v [58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_440 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_612 : (-word v [74, 10, 11, 26, 31, 73, 67, 32]) + word v [74, 10, 11, 26, 31, 73, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [25] * x) (rule_520 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_613 : word v [41, 43, 47, 7, 17, 21, 69, 8] + word v [41, 43, 47, 7, 17, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [73] * x) (rule_455 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_614 : word v [41, 43, 48, 51, 64, 36, 71, 73] + word v [41, 43, 47, 7, 17, 21, 69, 8]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 48, 51, 64, 36]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_473 v H)
  have h2 := congrArg (fun x : A => word v [23] * x) (rule_483 v H)
  have h3 := congrArg (fun x : A => word v [] * x) (rule_613 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (1) * h2 + (1) * h3
lemma rule_615 : (-word v [55, 27, 58, 33, 13, 49, 69, 8]) + word v [55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_484 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_616 : (-word v [55, 27, 58, 33, 13, 49, 69, 8]) + word v [55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 34, 63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_474 v H)
  have h2 := congrArg (fun x : A => word v [73] * x) (rule_456 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_617 : word v [27, 58, 33, 13, 49, 71, 72, 37] + (-word v [27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_512 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_618 : word v [43, 48, 51, 64, 36, 71, 72, 37] + word v [43, 47, 7, 17, 21, 69, 8, 66]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 48, 51, 64, 36, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_515 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_619 : word v [46, 48, 51, 64, 36, 71, 72, 37] + word v [45, 6, 7, 17, 21, 69, 8, 66]=0 := by
  have h0 := congrArg (fun x : A => x * word v [46, 48, 51, 64, 36, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_517 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_521 : word (a k) [3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  exact Universal.rule_521 (a k) (relation_zero k)
lemma rule_522 : word (a k) [37, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_522 (a k) (relation_zero k)
lemma rule_523 : word (a k) [66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_523 (a k) (relation_zero k)
lemma rule_524 : word (a k) [24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_524 (a k) (relation_zero k)
lemma rule_525 : word (a k) [28, 14, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_525 (a k) (relation_zero k)
lemma rule_526 : word (a k) [40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.rule_526 (a k) (relation_zero k)
lemma rule_527 : word (a k) [6, 7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.rule_527 (a k) (relation_zero k)
lemma rule_528 : word (a k) [47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.rule_528 (a k) (relation_zero k)
lemma rule_529 : word (a k) [58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.rule_529 (a k) (relation_zero k)
lemma rule_530 : word (a k) [21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_530 (a k) (relation_zero k)
lemma rule_531 : word (a k) [36, 70, 22, 3, 40, 62, 52, 42]=0 := by
  exact Universal.rule_531 (a k) (relation_zero k)
lemma rule_532 : word (a k) [21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_532 (a k) (relation_zero k)
lemma rule_533 : word (a k) [36, 70, 22, 3, 40, 60, 4, 55]=0 := by
  exact Universal.rule_533 (a k) (relation_zero k)
lemma rule_534 : word (a k) [49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_534 (a k) (relation_zero k)
lemma rule_535 : word (a k) [69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_535 (a k) (relation_zero k)
lemma rule_536 : word (a k) [70, 22, 3, 40, 60, 4, 56, 43]=0 := by
  exact Universal.rule_536 (a k) (relation_zero k)
lemma rule_537 : word (a k) [24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_537 (a k) (relation_zero k)
lemma rule_538 : word (a k) [28, 14, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_538 (a k) (relation_zero k)
lemma rule_539 : word (a k) [40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.rule_539 (a k) (relation_zero k)
lemma rule_540 : word (a k) [27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.rule_540 (a k) (relation_zero k)
lemma rule_541 : word (a k) [43, 47, 7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.rule_541 (a k) (relation_zero k)
lemma rule_542 : word (a k) [45, 6, 7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.rule_542 (a k) (relation_zero k)
lemma rule_543 : word (a k) [49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_543 (a k) (relation_zero k)
lemma rule_544 : word (a k) [8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_544 (a k) (relation_zero k)
lemma rule_545 : (-word (a k) [22, 3, 40, 60, 4, 54, 15, 1]) + word (a k) [22, 3, 40, 60, 4, 54, 16, 58]=0 := by
  exact Universal.rule_545 (a k) (relation_zero k)
lemma rule_546 : word (a k) [72, 37, 24, 19, 53, 54, 15, 1] + (-word (a k) [72, 37, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_546 (a k) (relation_zero k)
lemma rule_547 : word (a k) [8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_547 (a k) (relation_zero k)
lemma rule_548 : word (a k) [22, 3, 40, 60, 4, 54, 16, 59]=0 := by
  exact Universal.rule_548 (a k) (relation_zero k)
lemma rule_549 : word (a k) [72, 37, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_549 (a k) (relation_zero k)
lemma rule_550 : word (a k) [12, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.rule_550 (a k) (relation_zero k)
lemma rule_551 : word (a k) [61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.rule_551 (a k) (relation_zero k)
lemma rule_552 : (-word (a k) [13, 49, 69, 8, 66, 24, 18, 9]) + word (a k) [13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_552 (a k) (relation_zero k)
lemma rule_553 : (-word (a k) [17, 21, 69, 8, 66, 24, 18, 9]) + word (a k) [17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_553 (a k) (relation_zero k)
lemma rule_554 : (-word (a k) [63, 21, 69, 8, 66, 24, 18, 9]) + word (a k) [63, 21, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_554 (a k) (relation_zero k)
lemma rule_555 : word (a k) [4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.rule_555 (a k) (relation_zero k)
lemma rule_556 : word (a k) [9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_556 (a k) (relation_zero k)
lemma rule_557 : word (a k) [52, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_557 (a k) (relation_zero k)
lemma rule_558 : word (a k) [35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.rule_558 (a k) (relation_zero k)
lemma rule_559 : word (a k) [52, 41, 43, 47, 7, 17, 21, 71]=0 := by
  exact Universal.rule_559 (a k) (relation_zero k)
lemma rule_560 : word (a k) [27, 58, 34, 63, 21, 70, 22, 3] + word (a k) [27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  exact Universal.rule_560 (a k) (relation_zero k)
lemma rule_561 : word (a k) [43, 47, 7, 17, 21, 70, 22, 3] + (-word (a k) [43, 47, 7, 17, 21, 69, 8, 68])=0 := by
  exact Universal.rule_561 (a k) (relation_zero k)
lemma rule_562 : word (a k) [45, 6, 7, 17, 21, 70, 22, 3] + (-word (a k) [45, 6, 7, 17, 21, 69, 8, 68])=0 := by
  exact Universal.rule_562 (a k) (relation_zero k)
lemma rule_563 : word (a k) [7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_563 (a k) (relation_zero k)
lemma rule_564 : word (a k) [33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_564 (a k) (relation_zero k)
lemma rule_565 : word (a k) [50, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_565 (a k) (relation_zero k)
lemma rule_566 : (-word (a k) [7, 17, 21, 69, 8, 66, 24, 19]) + word (a k) [7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_566 (a k) (relation_zero k)
lemma rule_567 : (-word (a k) [33, 13, 49, 69, 8, 66, 24, 19]) + word (a k) [33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_567 (a k) (relation_zero k)
lemma rule_568 : (-word (a k) [50, 17, 21, 69, 8, 66, 24, 19]) + word (a k) [50, 17, 21, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_568 (a k) (relation_zero k)
lemma rule_569 : word (a k) [73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.rule_569 (a k) (relation_zero k)
lemma rule_570 : word (a k) [33, 13, 49, 71, 72, 38, 28, 14] + (-word (a k) [33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  exact Universal.rule_570 (a k) (relation_zero k)
lemma rule_571 : word (a k) [51, 64, 36, 71, 72, 38, 28, 14] + word (a k) [50, 17, 21, 69, 8, 66, 24, 18]=0 := by
  exact Universal.rule_571 (a k) (relation_zero k)
lemma rule_572 : word (a k) [10, 11, 26, 31, 73, 67, 32, 60]=0 := by
  exact Universal.rule_572 (a k) (relation_zero k)
lemma rule_573 : (-word (a k) [32, 61, 35, 55, 27, 58, 33, 13]) + word (a k) [32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  exact Universal.rule_573 (a k) (relation_zero k)
lemma rule_574 : (-word (a k) [39, 12, 35, 55, 27, 58, 33, 13]) + word (a k) [39, 12, 35, 55, 27, 58, 34, 65]=0 := by
  exact Universal.rule_574 (a k) (relation_zero k)
lemma rule_575 : word (a k) [26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  exact Universal.rule_575 (a k) (relation_zero k)
lemma rule_576 : word (a k) [35, 55, 27, 58, 34, 63, 21, 69] + word (a k) [35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  exact Universal.rule_576 (a k) (relation_zero k)
lemma rule_577 : word (a k) [52, 41, 43, 48, 51, 64, 36, 69]=0 := by
  exact Universal.rule_577 (a k) (relation_zero k)
lemma rule_578 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24] + word (a k) [48, 51, 64, 36, 71, 72, 38, 29]=0 := by
  exact Universal.rule_578 (a k) (relation_zero k)
lemma rule_579 : (-word (a k) [58, 33, 13, 49, 69, 8, 66, 24]) + word (a k) [58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  exact Universal.rule_579 (a k) (relation_zero k)
lemma rule_580 : word (a k) [10, 11, 26, 31, 73, 68, 39, 12] + (-word (a k) [10, 11, 26, 31, 73, 67, 32, 61])=0 := by
  exact Universal.rule_580 (a k) (relation_zero k)
lemma rule_581 : (-word (a k) [31, 73, 67, 32, 61, 35, 56, 43]) + word (a k) [31, 73, 67, 32, 62, 52, 42, 46]=0 := by
  exact Universal.rule_581 (a k) (relation_zero k)
lemma rule_582 : word (a k) [73, 67, 32, 61, 35, 56, 43, 48] + (-word (a k) [73, 67, 32, 61, 35, 55, 27, 59])=0 := by
  exact Universal.rule_582 (a k) (relation_zero k)
lemma rule_583 : word (a k) [73, 67, 32, 62, 52, 42, 45, 6] + (-word (a k) [73, 67, 32, 61, 35, 56, 43, 47])=0 := by
  exact Universal.rule_583 (a k) (relation_zero k)
lemma rule_584 : word (a k) [67, 32, 61, 35, 56, 43, 47, 7] + (-word (a k) [67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  exact Universal.rule_584 (a k) (relation_zero k)
lemma rule_585 : word (a k) [35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.rule_585 (a k) (relation_zero k)
lemma rule_586 : (-word (a k) [52, 41, 43, 47, 7, 17, 21, 70]) + word (a k) [52, 41, 43, 48, 51, 64, 36, 70]=0 := by
  exact Universal.rule_586 (a k) (relation_zero k)
lemma rule_587 : word (a k) [32, 61, 35, 55, 27, 59, 50, 17] + (-word (a k) [32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  exact Universal.rule_587 (a k) (relation_zero k)
lemma rule_588 : word (a k) [39, 12, 35, 55, 27, 59, 50, 17] + (-word (a k) [39, 12, 35, 55, 27, 58, 34, 63])=0 := by
  exact Universal.rule_588 (a k) (relation_zero k)
lemma rule_589 : (-word (a k) [21, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_589 (a k) (relation_zero k)
lemma rule_590 : word (a k) [26, 31, 73, 67, 32, 62, 52, 41] + (-word (a k) [26, 31, 73, 67, 32, 61, 35, 56])=0 := by
  exact Universal.rule_590 (a k) (relation_zero k)
lemma rule_591 : word (a k) [36, 70, 22, 3, 40, 62, 52, 41] + (-word (a k) [36, 70, 22, 3, 40, 60, 4, 56])=0 := by
  exact Universal.rule_591 (a k) (relation_zero k)
lemma rule_592 : (-word (a k) [49, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_592 (a k) (relation_zero k)
lemma rule_593 : (-word (a k) [31, 73, 67, 32, 61, 35, 55, 27]) + word (a k) [31, 73, 67, 32, 61, 35, 56, 44]=0 := by
  exact Universal.rule_593 (a k) (relation_zero k)
lemma rule_594 : word (a k) [69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_594 (a k) (relation_zero k)
lemma rule_595 : (-word (a k) [70, 22, 3, 40, 60, 4, 54, 16]) + word (a k) [70, 22, 3, 40, 60, 4, 56, 44]=0 := by
  exact Universal.rule_595 (a k) (relation_zero k)
lemma rule_596 : word (a k) [3, 40, 60, 4, 54, 16, 57, 5] + (-word (a k) [3, 40, 60, 4, 54, 15, 1, 34])=0 := by
  exact Universal.rule_596 (a k) (relation_zero k)
lemma rule_597 : (-word (a k) [37, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [37, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_597 (a k) (relation_zero k)
lemma rule_598 : (-word (a k) [66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_598 (a k) (relation_zero k)
lemma rule_599 : (-word (a k) [67, 32, 61, 35, 55, 27, 58, 34]) + word (a k) [67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  exact Universal.rule_599 (a k) (relation_zero k)
lemma rule_600 : (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35]) + word (a k) [11, 26, 31, 73, 67, 32, 62, 53]=0 := by
  exact Universal.rule_600 (a k) (relation_zero k)
lemma rule_601 : word (a k) [13, 49, 69, 8, 66, 25, 60, 4] + (-word (a k) [13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_601 (a k) (relation_zero k)
lemma rule_602 : word (a k) [17, 21, 69, 8, 66, 25, 60, 4] + (-word (a k) [17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_602 (a k) (relation_zero k)
lemma rule_603 : word (a k) [63, 21, 69, 8, 66, 25, 60, 4] + (-word (a k) [63, 21, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_603 (a k) (relation_zero k)
lemma rule_604 : (-word (a k) [12, 35, 55, 27, 58, 34, 63, 21]) + word (a k) [12, 35, 55, 27, 58, 34, 64, 36] + (-word (a k) [12, 35, 55, 27, 58, 33, 13, 49])=0 := by
  exact Universal.rule_604 (a k) (relation_zero k)
lemma rule_605 : word (a k) [14, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_605 (a k) (relation_zero k)
lemma rule_606 : word (a k) [18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_606 (a k) (relation_zero k)
lemma rule_607 : word (a k) [60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.rule_607 (a k) (relation_zero k)
lemma rule_608 : (-word (a k) [61, 35, 55, 27, 58, 34, 63, 21]) + word (a k) [61, 35, 55, 27, 58, 34, 64, 36] + (-word (a k) [61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  exact Universal.rule_608 (a k) (relation_zero k)
lemma rule_609 : word (a k) [6, 7, 17, 21, 69, 8, 66, 25] + word (a k) [6, 7, 17, 21, 69, 8, 68, 40]=0 := by
  exact Universal.rule_609 (a k) (relation_zero k)
lemma rule_610 : word (a k) [47, 7, 17, 21, 69, 8, 66, 25] + word (a k) [47, 7, 17, 21, 69, 8, 68, 40]=0 := by
  exact Universal.rule_610 (a k) (relation_zero k)
lemma rule_611 : word (a k) [58, 33, 13, 49, 69, 8, 66, 25] + word (a k) [58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  exact Universal.rule_611 (a k) (relation_zero k)
lemma rule_612 : (-word (a k) [74, 10, 11, 26, 31, 73, 67, 32]) + word (a k) [74, 10, 11, 26, 31, 73, 68, 40]=0 := by
  exact Universal.rule_612 (a k) (relation_zero k)
lemma rule_613 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8] + word (a k) [41, 43, 47, 7, 17, 21, 70, 23]=0 := by
  exact Universal.rule_613 (a k) (relation_zero k)
lemma rule_614 : word (a k) [41, 43, 48, 51, 64, 36, 71, 73] + word (a k) [41, 43, 47, 7, 17, 21, 69, 8]=0 := by
  exact Universal.rule_614 (a k) (relation_zero k)
lemma rule_615 : (-word (a k) [55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  exact Universal.rule_615 (a k) (relation_zero k)
lemma rule_616 : (-word (a k) [55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  exact Universal.rule_616 (a k) (relation_zero k)
lemma rule_617 : word (a k) [27, 58, 33, 13, 49, 71, 72, 37] + (-word (a k) [27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  exact Universal.rule_617 (a k) (relation_zero k)
lemma rule_618 : word (a k) [43, 48, 51, 64, 36, 71, 72, 37] + word (a k) [43, 47, 7, 17, 21, 69, 8, 66]=0 := by
  exact Universal.rule_618 (a k) (relation_zero k)
lemma rule_619 : word (a k) [46, 48, 51, 64, 36, 71, 72, 37] + word (a k) [45, 6, 7, 17, 21, 69, 8, 66]=0 := by
  exact Universal.rule_619 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
