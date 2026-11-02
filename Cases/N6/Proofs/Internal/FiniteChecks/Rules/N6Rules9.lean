import N6Rules8
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_620 : word v [8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_544 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_621 : word v [22, 3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [22, 3, 40, 60, 4, 54, 15]) (defining_0 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_622 : word v [72, 37, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_546 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_623 : word v [3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [3, 40, 60, 4, 54, 15]) (defining_1 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_624 : word v [37, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_443 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_597 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_625 : word v [66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_444 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_598 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_626 : word v [27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 34, 63, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_560 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_627 : word v [43, 47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_561 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_628 : word v [45, 6, 7, 17, 21, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_562 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_629 : word v [17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_245 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_410 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_464 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_553 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_630 : word v [63, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_246 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_411 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_465 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_554 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_631 : word v [13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_601 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_632 : word v [17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_602 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_633 : word v [63, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_603 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_634 : word v [21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_499 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_589 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_635 : word v [36, 70, 22, 3, 40, 60, 4, 56, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22, 3, 40, 60]) (defining_5 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_636 : word v [49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_502 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_592 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_637 : word v [3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [3, 40, 60, 4, 54, 16, 57]) (defining_7 v H)
  have h1 := congrArg (fun x : A => word v [65] * x) (rule_596 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_638 : word v [37, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_639 : word v [66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_640 : word v [41, 43, 47, 7, 17, 21, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_641 : word v [55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_642 : word v [13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 24, 18]) (defining_11 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_643 : word v [69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_594 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_644 : (-word v [70, 22, 3, 40, 60, 4, 54, 15, 1]) + word v [70, 22, 3, 40, 60, 4, 54, 16, 58]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22, 3, 40, 60, 4, 54]) (defining_12 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_645 : word v [69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_594 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_646 : word v [70, 22, 3, 40, 60, 4, 54, 16, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22, 3, 40, 60, 4, 54]) (defining_13 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_647 : word v [32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_587 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_648 : word v [39, 12, 35, 55, 27, 58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_588 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_649 : (-word v [7, 17, 21, 69, 8, 66, 24, 18, 9]) + word v [7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_650 : (-word v [33, 13, 49, 69, 8, 66, 24, 18, 9]) + word v [33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_651 : (-word v [50, 17, 21, 69, 8, 66, 24, 18, 9]) + word v [50, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_652 : word v [14, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [14, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_653 : word v [18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [18, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_654 : word v [60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [60, 4, 54, 15, 1, 34, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_655 : word v [12, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_656 : word v [61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_657 : word v [41, 43, 47, 7, 17, 21, 70, 22, 3] + (-word v [41, 43, 47, 7, 17, 21, 69, 8, 68])=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_613 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_658 : word v [55, 27, 58, 34, 63, 21, 70, 22, 3] + word v [55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 34, 63, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_616 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_659 : word v [6, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_660 : word v [47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_661 : word v [58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_662 : (-word v [6, 7, 17, 21, 69, 8, 66, 24, 19]) + word v [6, 7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_663 : (-word v [47, 7, 17, 21, 69, 8, 66, 24, 19]) + word v [47, 7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_664 : (-word v [58, 33, 13, 49, 69, 8, 66, 24, 19]) + word v [58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_665 : word v [31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55]) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_666 : word v [48, 51, 64, 36, 71, 72, 38, 28, 14] + word v [47, 7, 17, 21, 69, 8, 66, 24, 18]=0 := by
  have h0 := congrArg (fun x : A => x * word v [48, 51, 64, 36, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_578 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_667 : word v [58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word v [58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_579 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_668 : word v [74, 10, 11, 26, 31, 73, 67, 32, 60]=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 67]) (defining_27 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_669 : (-word v [67, 32, 61, 35, 55, 27, 58, 33, 13]) + word v [67, 32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_670 : word v [11, 26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 61]) (defining_29 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_671 : word v [12, 35, 55, 27, 58, 34, 63, 21, 69] + word v [12, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_604 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_672 : word v [61, 35, 55, 27, 58, 34, 63, 21, 69] + word v [61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_608 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_673 : (-word v [27, 58, 33, 13, 49, 69, 8, 66, 24]) + word v [27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_617 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_674 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24] + word v [43, 48, 51, 64, 36, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 48, 51, 64, 36, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_618 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_675 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24] + word v [46, 48, 51, 64, 36, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [46, 48, 51, 64, 36, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_619 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_676 : word v [74, 10, 11, 26, 31, 73, 68, 39, 12] + (-word v [74, 10, 11, 26, 31, 73, 67, 32, 61])=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 68]) (defining_32 v H)
  have h1 := congrArg (fun x : A => word v [61] * x) (rule_612 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_677 : (-word v [26, 31, 73, 67, 32, 61, 35, 56, 43]) + word v [26, 31, 73, 67, 32, 62, 52, 42, 46]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 62, 52]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [43] * x) (rule_590 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_678 : word v [31, 73, 67, 32, 61, 35, 56, 43, 48] + (-word v [31, 73, 67, 32, 61, 35, 55, 27, 59])=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 56]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_593 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_679 : word v [31, 73, 67, 32, 62, 52, 42, 45, 6] + (-word v [31, 73, 67, 32, 61, 35, 56, 43, 47])=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 62, 52, 42]) (defining_35 v H)
  have h1 := congrArg (fun x : A => word v [47] * x) (rule_581 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_680 : word v [73, 67, 32, 61, 35, 56, 43, 47, 7] + (-word v [73, 67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 56, 43]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [50] * x) (rule_582 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_681 : word v [12, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_682 : word v [61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_683 : word v [67, 32, 61, 35, 55, 27, 59, 50, 17] + (-word v [67, 32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_599 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_684 : word v [11, 26, 31, 73, 67, 32, 62, 52, 41] + (-word v [11, 26, 31, 73, 67, 32, 61, 35, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_600 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_685 : (-word v [13, 49, 69, 8, 66, 24, 18, 9, 41]) + word v [13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_552 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_686 : (-word v [17, 21, 69, 8, 66, 24, 18, 9, 41]) + word v [17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_553 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_687 : (-word v [63, 21, 69, 8, 66, 24, 18, 9, 41]) + word v [63, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_554 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_688 : word v [21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_532 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_589 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_689 : (-word v [26, 31, 73, 67, 32, 61, 35, 55, 27]) + word v [26, 31, 73, 67, 32, 61, 35, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [16] * x) (rule_575 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_690 : (-word v [36, 70, 22, 3, 40, 60, 4, 54, 16]) + word v [36, 70, 22, 3, 40, 60, 4, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22, 3, 40, 60, 4]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_533 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_691 : word v [49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_534 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_592 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_692 : (-word v [8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_547 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_693 : word v [22, 3, 40, 60, 4, 54, 16, 57, 5] + (-word v [22, 3, 40, 60, 4, 54, 15, 1, 34])=0 := by
  have h0 := congrArg (fun x : A => x * word v [22, 3, 40, 60, 4, 54, 16]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [34] * x) (rule_545 v H)
  have h2 := congrArg (fun x : A => word v [51] * x) (rule_548 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_694 : (-word v [72, 37, 24, 18, 9, 41, 44, 57, 5]) + word v [72, 37, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_549 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_695 : (-word v [73, 67, 32, 61, 35, 55, 27, 58, 34]) + word v [73, 67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_569 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_696 : word v [7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word v [7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_563 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_566 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_697 : (-word v [10, 11, 26, 31, 73, 67, 32, 61, 35]) + word v [10, 11, 26, 31, 73, 67, 32, 62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [4] * x) (rule_572 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_698 : word v [33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word v [33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_564 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_567 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_699 : word v [50, 17, 21, 69, 8, 66, 25, 60, 4] + (-word v [50, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_565 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_568 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_700 : word v [24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_524 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_537 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_701 : word v [28, 14, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [28, 14, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_525 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_538 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_702 : (-word v [32, 61, 35, 55, 27, 58, 34, 63, 21]) + word v [32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word v [32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_573 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_703 : (-word v [39, 12, 35, 55, 27, 58, 34, 63, 21]) + word v [39, 12, 35, 55, 27, 58, 34, 64, 36] + (-word v [39, 12, 35, 55, 27, 58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_574 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_704 : word v [40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 60, 4, 54, 15, 1, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_526 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_539 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_705 : word v [27, 58, 33, 13, 49, 69, 8, 66, 25] + word v [27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_540 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_706 : word v [43, 47, 7, 17, 21, 69, 8, 66, 25] + word v [43, 47, 7, 17, 21, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_541 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_707 : word v [45, 6, 7, 17, 21, 69, 8, 66, 25] + word v [45, 6, 7, 17, 21, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_542 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_708 : (-word v [35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_585 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_709 : (-word v [35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 34, 63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_576 v H)
  have h2 := congrArg (fun x : A => word v [73] * x) (rule_558 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_710 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8] + word v [52, 41, 43, 47, 7, 17, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [73] * x) (rule_559 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_711 : word v [52, 41, 43, 48, 51, 64, 36, 71, 73] + word v [52, 41, 43, 47, 7, 17, 21, 69, 8]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 48, 51, 64, 36]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_577 v H)
  have h2 := congrArg (fun x : A => word v [23] * x) (rule_586 v H)
  have h3 := congrArg (fun x : A => word v [] * x) (rule_710 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (1) * h2 + (1) * h3
lemma rule_712 : word v [41, 43, 48, 51, 64, 36, 71, 72, 37] + word v [41, 43, 47, 7, 17, 21, 69, 8, 66]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 48, 51, 64, 36, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_614 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_713 : word v [55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word v [55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_615 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_620 : word (a k) [8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_620 (a k) (relation_zero k)
lemma rule_621 : word (a k) [22, 3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  exact Universal.rule_621 (a k) (relation_zero k)
lemma rule_622 : word (a k) [72, 37, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_622 (a k) (relation_zero k)
lemma rule_623 : word (a k) [3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.rule_623 (a k) (relation_zero k)
lemma rule_624 : word (a k) [37, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_624 (a k) (relation_zero k)
lemma rule_625 : word (a k) [66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_625 (a k) (relation_zero k)
lemma rule_626 : word (a k) [27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.rule_626 (a k) (relation_zero k)
lemma rule_627 : word (a k) [43, 47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.rule_627 (a k) (relation_zero k)
lemma rule_628 : word (a k) [45, 6, 7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.rule_628 (a k) (relation_zero k)
lemma rule_629 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_629 (a k) (relation_zero k)
lemma rule_630 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_630 (a k) (relation_zero k)
lemma rule_631 : word (a k) [13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_631 (a k) (relation_zero k)
lemma rule_632 : word (a k) [17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_632 (a k) (relation_zero k)
lemma rule_633 : word (a k) [63, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_633 (a k) (relation_zero k)
lemma rule_634 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_634 (a k) (relation_zero k)
lemma rule_635 : word (a k) [36, 70, 22, 3, 40, 60, 4, 56, 43]=0 := by
  exact Universal.rule_635 (a k) (relation_zero k)
lemma rule_636 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_636 (a k) (relation_zero k)
lemma rule_637 : word (a k) [3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.rule_637 (a k) (relation_zero k)
lemma rule_638 : word (a k) [37, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_638 (a k) (relation_zero k)
lemma rule_639 : word (a k) [66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_639 (a k) (relation_zero k)
lemma rule_640 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.rule_640 (a k) (relation_zero k)
lemma rule_641 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.rule_641 (a k) (relation_zero k)
lemma rule_642 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_642 (a k) (relation_zero k)
lemma rule_643 : word (a k) [69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_643 (a k) (relation_zero k)
lemma rule_644 : (-word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1]) + word (a k) [70, 22, 3, 40, 60, 4, 54, 16, 58]=0 := by
  exact Universal.rule_644 (a k) (relation_zero k)
lemma rule_645 : word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_645 (a k) (relation_zero k)
lemma rule_646 : word (a k) [70, 22, 3, 40, 60, 4, 54, 16, 59]=0 := by
  exact Universal.rule_646 (a k) (relation_zero k)
lemma rule_647 : word (a k) [32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.rule_647 (a k) (relation_zero k)
lemma rule_648 : word (a k) [39, 12, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.rule_648 (a k) (relation_zero k)
lemma rule_649 : (-word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9]) + word (a k) [7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_649 (a k) (relation_zero k)
lemma rule_650 : (-word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9]) + word (a k) [33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_650 (a k) (relation_zero k)
lemma rule_651 : (-word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9]) + word (a k) [50, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_651 (a k) (relation_zero k)
lemma rule_652 : word (a k) [14, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_652 (a k) (relation_zero k)
lemma rule_653 : word (a k) [18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_653 (a k) (relation_zero k)
lemma rule_654 : word (a k) [60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.rule_654 (a k) (relation_zero k)
lemma rule_655 : word (a k) [12, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.rule_655 (a k) (relation_zero k)
lemma rule_656 : word (a k) [61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.rule_656 (a k) (relation_zero k)
lemma rule_657 : word (a k) [41, 43, 47, 7, 17, 21, 70, 22, 3] + (-word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 68])=0 := by
  exact Universal.rule_657 (a k) (relation_zero k)
lemma rule_658 : word (a k) [55, 27, 58, 34, 63, 21, 70, 22, 3] + word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  exact Universal.rule_658 (a k) (relation_zero k)
lemma rule_659 : word (a k) [6, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_659 (a k) (relation_zero k)
lemma rule_660 : word (a k) [47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_660 (a k) (relation_zero k)
lemma rule_661 : word (a k) [58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_661 (a k) (relation_zero k)
lemma rule_662 : (-word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19]) + word (a k) [6, 7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_662 (a k) (relation_zero k)
lemma rule_663 : (-word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19]) + word (a k) [47, 7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_663 (a k) (relation_zero k)
lemma rule_664 : (-word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19]) + word (a k) [58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_664 (a k) (relation_zero k)
lemma rule_665 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.rule_665 (a k) (relation_zero k)
lemma rule_666 : word (a k) [48, 51, 64, 36, 71, 72, 38, 28, 14] + word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18]=0 := by
  exact Universal.rule_666 (a k) (relation_zero k)
lemma rule_667 : word (a k) [58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  exact Universal.rule_667 (a k) (relation_zero k)
lemma rule_668 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 60]=0 := by
  exact Universal.rule_668 (a k) (relation_zero k)
lemma rule_669 : (-word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13]) + word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  exact Universal.rule_669 (a k) (relation_zero k)
lemma rule_670 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  exact Universal.rule_670 (a k) (relation_zero k)
lemma rule_671 : word (a k) [12, 35, 55, 27, 58, 34, 63, 21, 69] + word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  exact Universal.rule_671 (a k) (relation_zero k)
lemma rule_672 : word (a k) [61, 35, 55, 27, 58, 34, 63, 21, 69] + word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  exact Universal.rule_672 (a k) (relation_zero k)
lemma rule_673 : (-word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24]) + word (a k) [27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  exact Universal.rule_673 (a k) (relation_zero k)
lemma rule_674 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24] + word (a k) [43, 48, 51, 64, 36, 71, 72, 38, 29]=0 := by
  exact Universal.rule_674 (a k) (relation_zero k)
lemma rule_675 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24] + word (a k) [46, 48, 51, 64, 36, 71, 72, 38, 29]=0 := by
  exact Universal.rule_675 (a k) (relation_zero k)
lemma rule_676 : word (a k) [74, 10, 11, 26, 31, 73, 68, 39, 12] + (-word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61])=0 := by
  exact Universal.rule_676 (a k) (relation_zero k)
lemma rule_677 : (-word (a k) [26, 31, 73, 67, 32, 61, 35, 56, 43]) + word (a k) [26, 31, 73, 67, 32, 62, 52, 42, 46]=0 := by
  exact Universal.rule_677 (a k) (relation_zero k)
lemma rule_678 : word (a k) [31, 73, 67, 32, 61, 35, 56, 43, 48] + (-word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 59])=0 := by
  exact Universal.rule_678 (a k) (relation_zero k)
lemma rule_679 : word (a k) [31, 73, 67, 32, 62, 52, 42, 45, 6] + (-word (a k) [31, 73, 67, 32, 61, 35, 56, 43, 47])=0 := by
  exact Universal.rule_679 (a k) (relation_zero k)
lemma rule_680 : word (a k) [73, 67, 32, 61, 35, 56, 43, 47, 7] + (-word (a k) [73, 67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  exact Universal.rule_680 (a k) (relation_zero k)
lemma rule_681 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.rule_681 (a k) (relation_zero k)
lemma rule_682 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.rule_682 (a k) (relation_zero k)
lemma rule_683 : word (a k) [67, 32, 61, 35, 55, 27, 59, 50, 17] + (-word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  exact Universal.rule_683 (a k) (relation_zero k)
lemma rule_684 : word (a k) [11, 26, 31, 73, 67, 32, 62, 52, 41] + (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 56])=0 := by
  exact Universal.rule_684 (a k) (relation_zero k)
lemma rule_685 : (-word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_685 (a k) (relation_zero k)
lemma rule_686 : (-word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_686 (a k) (relation_zero k)
lemma rule_687 : (-word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [63, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_687 (a k) (relation_zero k)
lemma rule_688 : word (a k) [21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_688 (a k) (relation_zero k)
lemma rule_689 : (-word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27]) + word (a k) [26, 31, 73, 67, 32, 61, 35, 56, 44]=0 := by
  exact Universal.rule_689 (a k) (relation_zero k)
lemma rule_690 : (-word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 16]) + word (a k) [36, 70, 22, 3, 40, 60, 4, 56, 44]=0 := by
  exact Universal.rule_690 (a k) (relation_zero k)
lemma rule_691 : word (a k) [49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_691 (a k) (relation_zero k)
lemma rule_692 : (-word (a k) [8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_692 (a k) (relation_zero k)
lemma rule_693 : word (a k) [22, 3, 40, 60, 4, 54, 16, 57, 5] + (-word (a k) [22, 3, 40, 60, 4, 54, 15, 1, 34])=0 := by
  exact Universal.rule_693 (a k) (relation_zero k)
lemma rule_694 : (-word (a k) [72, 37, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [72, 37, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_694 (a k) (relation_zero k)
lemma rule_695 : (-word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34]) + word (a k) [73, 67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  exact Universal.rule_695 (a k) (relation_zero k)
lemma rule_696 : word (a k) [7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word (a k) [7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_696 (a k) (relation_zero k)
lemma rule_697 : (-word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35]) + word (a k) [10, 11, 26, 31, 73, 67, 32, 62, 53]=0 := by
  exact Universal.rule_697 (a k) (relation_zero k)
lemma rule_698 : word (a k) [33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word (a k) [33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_698 (a k) (relation_zero k)
lemma rule_699 : word (a k) [50, 17, 21, 69, 8, 66, 25, 60, 4] + (-word (a k) [50, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_699 (a k) (relation_zero k)
lemma rule_700 : word (a k) [24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_700 (a k) (relation_zero k)
lemma rule_701 : word (a k) [28, 14, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_701 (a k) (relation_zero k)
lemma rule_702 : (-word (a k) [32, 61, 35, 55, 27, 58, 34, 63, 21]) + word (a k) [32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  exact Universal.rule_702 (a k) (relation_zero k)
lemma rule_703 : (-word (a k) [39, 12, 35, 55, 27, 58, 34, 63, 21]) + word (a k) [39, 12, 35, 55, 27, 58, 34, 64, 36] + (-word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49])=0 := by
  exact Universal.rule_703 (a k) (relation_zero k)
lemma rule_704 : word (a k) [40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.rule_704 (a k) (relation_zero k)
lemma rule_705 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 25] + word (a k) [27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  exact Universal.rule_705 (a k) (relation_zero k)
lemma rule_706 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 25] + word (a k) [43, 47, 7, 17, 21, 69, 8, 68, 40]=0 := by
  exact Universal.rule_706 (a k) (relation_zero k)
lemma rule_707 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 25] + word (a k) [45, 6, 7, 17, 21, 69, 8, 68, 40]=0 := by
  exact Universal.rule_707 (a k) (relation_zero k)
lemma rule_708 : (-word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  exact Universal.rule_708 (a k) (relation_zero k)
lemma rule_709 : (-word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  exact Universal.rule_709 (a k) (relation_zero k)
lemma rule_710 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8] + word (a k) [52, 41, 43, 47, 7, 17, 21, 70, 23]=0 := by
  exact Universal.rule_710 (a k) (relation_zero k)
lemma rule_711 : word (a k) [52, 41, 43, 48, 51, 64, 36, 71, 73] + word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8]=0 := by
  exact Universal.rule_711 (a k) (relation_zero k)
lemma rule_712 : word (a k) [41, 43, 48, 51, 64, 36, 71, 72, 37] + word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66]=0 := by
  exact Universal.rule_712 (a k) (relation_zero k)
lemma rule_713 : word (a k) [55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  exact Universal.rule_713 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
