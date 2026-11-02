import N6Rules9
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_714 : word v [69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_643 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_715 : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22, 3, 40, 60, 4, 54, 15]) (defining_0 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_716 : word v [8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_544 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_692 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_717 : word v [22, 3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [22, 3, 40, 60, 4, 54, 15]) (defining_1 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_718 : word v [72, 37, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_546 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_694 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_719 : word v [41, 43, 47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_657 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_720 : word v [55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 34, 63, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_658 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_721 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_352 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_508 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_566 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_649 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_722 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [34, 63, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_353 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_510 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_567 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_650 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_723 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_354 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_511 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_568 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_651 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_724 : word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_696 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_725 : word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_698 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_726 : word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_699 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_727 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_601 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_685 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_728 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_602 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_686 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_729 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_603 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_687 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_730 : word v [8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_731 : word v [22, 3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [22, 3, 40, 60, 4, 54, 16, 57]) (defining_7 v H)
  have h1 := congrArg (fun x : A => word v [65] * x) (rule_693 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_732 : word v [72, 37, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_733 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_734 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_735 : word v [21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_688 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_736 : (-word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1]) + word v [36, 70, 22, 3, 40, 60, 4, 54, 16, 58]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22, 3, 40, 60, 4, 54]) (defining_12 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_737 : word v [49, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_691 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_738 : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_688 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_739 : word v [36, 70, 22, 3, 40, 60, 4, 54, 16, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22, 3, 40, 60, 4, 54]) (defining_13 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_740 : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_691 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_741 : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_683 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_742 : (-word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9]) + word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_743 : (-word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9]) + word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_744 : (-word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_745 : word v [24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [24, 18, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_746 : word v [28, 14, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [28, 14, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_747 : word v [40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 60, 4, 54, 15, 1, 34, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_748 : word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_749 : word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_750 : word v [35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 34, 63, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_709 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_751 : word v [52, 41, 43, 47, 7, 17, 21, 70, 22, 3] + (-word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 68])=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_710 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_752 : word v [27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_753 : word v [43, 47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_754 : word v [45, 6, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_755 : (-word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word v [27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_756 : (-word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19]) + word v [43, 47, 7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_757 : (-word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19]) + word v [45, 6, 7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_758 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 55]) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_759 : word v [27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_673 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_760 : word v [43, 48, 51, 64, 36, 71, 72, 38, 28, 14] + word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 48, 51, 64, 36, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_674 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_761 : word v [46, 48, 51, 64, 36, 71, 72, 38, 28, 14] + word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18]=0 := by
  have h0 := congrArg (fun x : A => x * word v [46, 48, 51, 64, 36, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_675 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_762 : (-word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) + word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_763 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 61]) (defining_29 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_764 : word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 69] + word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_702 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_765 : word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 69] + word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_703 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_766 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24] + word v [41, 43, 48, 51, 64, 36, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 48, 51, 64, 36, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_712 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_767 : (-word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word v [55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_713 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_768 : (-word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 43]) + word v [11, 26, 31, 73, 67, 32, 62, 52, 42, 46]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 62, 52]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [43] * x) (rule_684 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_769 : word v [26, 31, 73, 67, 32, 61, 35, 56, 43, 48] + (-word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59])=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 56]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_689 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_770 : word v [26, 31, 73, 67, 32, 62, 52, 42, 45, 6] + (-word v [26, 31, 73, 67, 32, 61, 35, 56, 43, 47])=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 62, 52, 42]) (defining_35 v H)
  have h1 := congrArg (fun x : A => word v [47] * x) (rule_677 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_771 : word v [31, 73, 67, 32, 61, 35, 56, 43, 47, 7] + (-word v [31, 73, 67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 56, 43]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [50] * x) (rule_678 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_772 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_773 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_774 : word v [73, 67, 32, 61, 35, 55, 27, 59, 50, 17] + (-word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_695 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_775 : (-word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_649 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_776 : word v [10, 11, 26, 31, 73, 67, 32, 62, 52, 41] + (-word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_697 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_777 : (-word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_650 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_778 : (-word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_651 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_779 : (-word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27]) + word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 61, 35]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [16] * x) (rule_670 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_780 : word v [13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_631 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_685 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_781 : word v [17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_632 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_686 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_782 : word v [63, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_633 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_687 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_783 : (-word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) + word v [31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55, 27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_665 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_784 : (-word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_645 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_785 : word v [70, 22, 3, 40, 60, 4, 54, 16, 57, 5] + (-word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34])=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22, 3, 40, 60, 4, 54, 16]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [34] * x) (rule_644 v H)
  have h2 := congrArg (fun x : A => word v [51] * x) (rule_646 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_786 : word v [6, 7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_659 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_662 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_787 : word v [47, 7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_660 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_663 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_788 : word v [58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_661 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_664 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_789 : (-word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35]) + word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 67, 32]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [4] * x) (rule_668 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_790 : word v [3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [3, 40, 60, 4, 54, 15, 1, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_623 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_637 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_791 : word v [37, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_624 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_638 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_792 : word v [66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_625 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_639 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_793 : (-word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) + word v [67, 32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_669 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_794 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25] + word v [41, 43, 47, 7, 17, 21, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_640 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_795 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word v [55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_641 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_796 : (-word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 33, 13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_681 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_797 : (-word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [12, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 34, 63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_671 v H)
  have h2 := congrArg (fun x : A => word v [73] * x) (rule_655 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_798 : (-word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 33, 13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_682 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_799 : (-word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 34, 63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_672 v H)
  have h2 := congrArg (fun x : A => word v [73] * x) (rule_656 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_800 : word v [35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_708 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_801 : word v [52, 41, 43, 48, 51, 64, 36, 71, 72, 37] + word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 48, 51, 64, 36, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_711 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_714 : word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_714 (a k) (relation_zero k)
lemma rule_715 : word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  exact Universal.rule_715 (a k) (relation_zero k)
lemma rule_716 : word (a k) [8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_716 (a k) (relation_zero k)
lemma rule_717 : word (a k) [22, 3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.rule_717 (a k) (relation_zero k)
lemma rule_718 : word (a k) [72, 37, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_718 (a k) (relation_zero k)
lemma rule_719 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.rule_719 (a k) (relation_zero k)
lemma rule_720 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.rule_720 (a k) (relation_zero k)
lemma rule_721 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_721 (a k) (relation_zero k)
lemma rule_722 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_722 (a k) (relation_zero k)
lemma rule_723 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_723 (a k) (relation_zero k)
lemma rule_724 : word (a k) [7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_724 (a k) (relation_zero k)
lemma rule_725 : word (a k) [33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_725 (a k) (relation_zero k)
lemma rule_726 : word (a k) [50, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_726 (a k) (relation_zero k)
lemma rule_727 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_727 (a k) (relation_zero k)
lemma rule_728 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_728 (a k) (relation_zero k)
lemma rule_729 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_729 (a k) (relation_zero k)
lemma rule_730 : word (a k) [8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_730 (a k) (relation_zero k)
lemma rule_731 : word (a k) [22, 3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.rule_731 (a k) (relation_zero k)
lemma rule_732 : word (a k) [72, 37, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_732 (a k) (relation_zero k)
lemma rule_733 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.rule_733 (a k) (relation_zero k)
lemma rule_734 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.rule_734 (a k) (relation_zero k)
lemma rule_735 : word (a k) [21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_735 (a k) (relation_zero k)
lemma rule_736 : (-word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1]) + word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 16, 58]=0 := by
  exact Universal.rule_736 (a k) (relation_zero k)
lemma rule_737 : word (a k) [49, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_737 (a k) (relation_zero k)
lemma rule_738 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_738 (a k) (relation_zero k)
lemma rule_739 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 16, 59]=0 := by
  exact Universal.rule_739 (a k) (relation_zero k)
lemma rule_740 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_740 (a k) (relation_zero k)
lemma rule_741 : word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.rule_741 (a k) (relation_zero k)
lemma rule_742 : (-word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9]) + word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_742 (a k) (relation_zero k)
lemma rule_743 : (-word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9]) + word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_743 (a k) (relation_zero k)
lemma rule_744 : (-word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_744 (a k) (relation_zero k)
lemma rule_745 : word (a k) [24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_745 (a k) (relation_zero k)
lemma rule_746 : word (a k) [28, 14, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_746 (a k) (relation_zero k)
lemma rule_747 : word (a k) [40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.rule_747 (a k) (relation_zero k)
lemma rule_748 : word (a k) [32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.rule_748 (a k) (relation_zero k)
lemma rule_749 : word (a k) [39, 12, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.rule_749 (a k) (relation_zero k)
lemma rule_750 : word (a k) [35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  exact Universal.rule_750 (a k) (relation_zero k)
lemma rule_751 : word (a k) [52, 41, 43, 47, 7, 17, 21, 70, 22, 3] + (-word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 68])=0 := by
  exact Universal.rule_751 (a k) (relation_zero k)
lemma rule_752 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_752 (a k) (relation_zero k)
lemma rule_753 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_753 (a k) (relation_zero k)
lemma rule_754 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_754 (a k) (relation_zero k)
lemma rule_755 : (-word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_755 (a k) (relation_zero k)
lemma rule_756 : (-word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19]) + word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_756 (a k) (relation_zero k)
lemma rule_757 : (-word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19]) + word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_757 (a k) (relation_zero k)
lemma rule_758 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.rule_758 (a k) (relation_zero k)
lemma rule_759 : word (a k) [27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  exact Universal.rule_759 (a k) (relation_zero k)
lemma rule_760 : word (a k) [43, 48, 51, 64, 36, 71, 72, 38, 28, 14] + word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18]=0 := by
  exact Universal.rule_760 (a k) (relation_zero k)
lemma rule_761 : word (a k) [46, 48, 51, 64, 36, 71, 72, 38, 28, 14] + word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18]=0 := by
  exact Universal.rule_761 (a k) (relation_zero k)
lemma rule_762 : (-word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) + word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  exact Universal.rule_762 (a k) (relation_zero k)
lemma rule_763 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  exact Universal.rule_763 (a k) (relation_zero k)
lemma rule_764 : word (a k) [32, 61, 35, 55, 27, 58, 34, 63, 21, 69] + word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  exact Universal.rule_764 (a k) (relation_zero k)
lemma rule_765 : word (a k) [39, 12, 35, 55, 27, 58, 34, 63, 21, 69] + word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  exact Universal.rule_765 (a k) (relation_zero k)
lemma rule_766 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24] + word (a k) [41, 43, 48, 51, 64, 36, 71, 72, 38, 29]=0 := by
  exact Universal.rule_766 (a k) (relation_zero k)
lemma rule_767 : (-word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word (a k) [55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  exact Universal.rule_767 (a k) (relation_zero k)
lemma rule_768 : (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 56, 43]) + word (a k) [11, 26, 31, 73, 67, 32, 62, 52, 42, 46]=0 := by
  exact Universal.rule_768 (a k) (relation_zero k)
lemma rule_769 : word (a k) [26, 31, 73, 67, 32, 61, 35, 56, 43, 48] + (-word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 59])=0 := by
  exact Universal.rule_769 (a k) (relation_zero k)
lemma rule_770 : word (a k) [26, 31, 73, 67, 32, 62, 52, 42, 45, 6] + (-word (a k) [26, 31, 73, 67, 32, 61, 35, 56, 43, 47])=0 := by
  exact Universal.rule_770 (a k) (relation_zero k)
lemma rule_771 : word (a k) [31, 73, 67, 32, 61, 35, 56, 43, 47, 7] + (-word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  exact Universal.rule_771 (a k) (relation_zero k)
lemma rule_772 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.rule_772 (a k) (relation_zero k)
lemma rule_773 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.rule_773 (a k) (relation_zero k)
lemma rule_774 : word (a k) [73, 67, 32, 61, 35, 55, 27, 59, 50, 17] + (-word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  exact Universal.rule_774 (a k) (relation_zero k)
lemma rule_775 : (-word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_775 (a k) (relation_zero k)
lemma rule_776 : word (a k) [10, 11, 26, 31, 73, 67, 32, 62, 52, 41] + (-word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 56])=0 := by
  exact Universal.rule_776 (a k) (relation_zero k)
lemma rule_777 : (-word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_777 (a k) (relation_zero k)
lemma rule_778 : (-word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [50, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_778 (a k) (relation_zero k)
lemma rule_779 : (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27]) + word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 56, 44]=0 := by
  exact Universal.rule_779 (a k) (relation_zero k)
lemma rule_780 : word (a k) [13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_780 (a k) (relation_zero k)
lemma rule_781 : word (a k) [17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_781 (a k) (relation_zero k)
lemma rule_782 : word (a k) [63, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_782 (a k) (relation_zero k)
lemma rule_783 : (-word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) + word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  exact Universal.rule_783 (a k) (relation_zero k)
lemma rule_784 : (-word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_784 (a k) (relation_zero k)
lemma rule_785 : word (a k) [70, 22, 3, 40, 60, 4, 54, 16, 57, 5] + (-word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1, 34])=0 := by
  exact Universal.rule_785 (a k) (relation_zero k)
lemma rule_786 : word (a k) [6, 7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_786 (a k) (relation_zero k)
lemma rule_787 : word (a k) [47, 7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_787 (a k) (relation_zero k)
lemma rule_788 : word (a k) [58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_788 (a k) (relation_zero k)
lemma rule_789 : (-word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35]) + word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 62, 53]=0 := by
  exact Universal.rule_789 (a k) (relation_zero k)
lemma rule_790 : word (a k) [3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.rule_790 (a k) (relation_zero k)
lemma rule_791 : word (a k) [37, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_791 (a k) (relation_zero k)
lemma rule_792 : word (a k) [66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_792 (a k) (relation_zero k)
lemma rule_793 : (-word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) + word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  exact Universal.rule_793 (a k) (relation_zero k)
lemma rule_794 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 25] + word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 68, 40]=0 := by
  exact Universal.rule_794 (a k) (relation_zero k)
lemma rule_795 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  exact Universal.rule_795 (a k) (relation_zero k)
lemma rule_796 : (-word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  exact Universal.rule_796 (a k) (relation_zero k)
lemma rule_797 : (-word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [12, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  exact Universal.rule_797 (a k) (relation_zero k)
lemma rule_798 : (-word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  exact Universal.rule_798 (a k) (relation_zero k)
lemma rule_799 : (-word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  exact Universal.rule_799 (a k) (relation_zero k)
lemma rule_800 : word (a k) [35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  exact Universal.rule_800 (a k) (relation_zero k)
lemma rule_801 : word (a k) [52, 41, 43, 48, 51, 64, 36, 71, 72, 37] + word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66]=0 := by
  exact Universal.rule_801 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
