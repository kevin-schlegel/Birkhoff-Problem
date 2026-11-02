import N6Rules10
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_802 : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_735 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_803 : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22, 3, 40, 60, 4, 54, 15]) (defining_0 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_804 : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_737 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_805 : word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_643 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_784 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_806 : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22, 3, 40, 60, 4, 54, 15]) (defining_1 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_807 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 34, 63, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_750 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_808 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_751 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_809 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_457 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_609 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_662 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_742 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_810 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_458 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_610 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_663 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_743 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_811 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 34, 63, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_459 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_611 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_664 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_744 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_812 : word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_786 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_813 : word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_787 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_814 : word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_788 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_815 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_696 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_775 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_816 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_698 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_777 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_817 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_699 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_778 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_818 : word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_819 : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22, 3, 40, 60, 4, 54, 16, 57]) (defining_7 v H)
  have h1 := congrArg (fun x : A => word v [65] * x) (rule_785 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_820 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 33, 13, 49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_821 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 33, 13, 49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_822 : word v [13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_780 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_823 : word v [17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_781 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_824 : word v [63, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_782 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_825 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_780 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_826 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_781 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_827 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_782 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_828 : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_774 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_829 : (-word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_830 : (-word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]) + word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_831 : (-word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9]) + word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_832 : word v [3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [3, 40, 60, 4, 54, 15, 1, 34, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_833 : word v [37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 24, 18, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_834 : word v [66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 24, 18, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_835 : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_836 : word v [12, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 34, 63, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_797 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_837 : word v [61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 34, 63, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_799 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_838 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_839 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_840 : (-word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19]) + word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_841 : (-word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_842 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 61, 35, 55]) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_843 : word v [41, 43, 48, 51, 64, 36, 71, 72, 38, 28, 14] + word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 48, 51, 64, 36, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_766 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_844 : word v [55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_767 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_845 : (-word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) + word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55, 27, 58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_846 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 67, 32, 61]) (defining_29 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_847 : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69] + word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_793 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_848 : (-word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word v [35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_800 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_849 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24] + word v [52, 41, 43, 48, 51, 64, 36, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 48, 51, 64, 36, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_801 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_850 : (-word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43]) + word v [10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 46]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 62, 52]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [43] * x) (rule_776 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_851 : word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48] + (-word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59])=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 61, 35, 56]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_779 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_852 : word v [11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6] + (-word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47])=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 62, 52, 42]) (defining_35 v H)
  have h1 := congrArg (fun x : A => word v [47] * x) (rule_768 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_853 : word v [26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7] + (-word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 56, 43]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [50] * x) (rule_769 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_854 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_855 : word v [31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17] + (-word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55, 27, 59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_783 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_856 : (-word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_742 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_857 : (-word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_743 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_858 : (-word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_744 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_859 : word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 41] + (-word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 67, 32, 62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_789 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_860 : word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_724 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_775 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_861 : (-word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27]) + word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 61, 35]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [16] * x) (rule_763 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_862 : word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_725 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_777 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_863 : word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_726 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_778 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_864 : (-word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_738 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_865 : (-word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) + word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 55, 27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_758 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_866 : word v [36, 70, 22, 3, 40, 60, 4, 54, 16, 57, 5] + (-word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34])=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22, 3, 40, 60, 4, 54, 16]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [34] * x) (rule_736 v H)
  have h2 := congrArg (fun x : A => word v [51] * x) (rule_739 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_867 : (-word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_740 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_868 : word v [27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_752 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_755 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_869 : word v [43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_753 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_756 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_870 : word v [45, 6, 7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_754 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_757 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_871 : word v [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_716 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_730 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_872 : word v [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [22, 3, 40, 60, 4, 54, 15, 1, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_717 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_731 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_873 : word v [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_718 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_732 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_874 : (-word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) + word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_762 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_875 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_733 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_876 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25] + word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_734 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_877 : (-word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 33, 13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_772 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_878 : (-word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 34, 63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_764 v H)
  have h2 := congrArg (fun x : A => word v [73] * x) (rule_748 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_879 : (-word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 33, 13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_773 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_880 : (-word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 34, 63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_765 v H)
  have h2 := congrArg (fun x : A => word v [73] * x) (rule_749 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_881 : word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 33, 13, 49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_796 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_882 : word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 33, 13, 49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_798 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_802 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_802 (a k) (relation_zero k)
lemma rule_803 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 33]=0 := by
  exact Universal.rule_803 (a k) (relation_zero k)
lemma rule_804 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_804 (a k) (relation_zero k)
lemma rule_805 : word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_805 (a k) (relation_zero k)
lemma rule_806 : word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.rule_806 (a k) (relation_zero k)
lemma rule_807 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.rule_807 (a k) (relation_zero k)
lemma rule_808 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.rule_808 (a k) (relation_zero k)
lemma rule_809 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_809 (a k) (relation_zero k)
lemma rule_810 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_810 (a k) (relation_zero k)
lemma rule_811 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_811 (a k) (relation_zero k)
lemma rule_812 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_812 (a k) (relation_zero k)
lemma rule_813 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_813 (a k) (relation_zero k)
lemma rule_814 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_814 (a k) (relation_zero k)
lemma rule_815 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_815 (a k) (relation_zero k)
lemma rule_816 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_816 (a k) (relation_zero k)
lemma rule_817 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_817 (a k) (relation_zero k)
lemma rule_818 : word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_818 (a k) (relation_zero k)
lemma rule_819 : word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.rule_819 (a k) (relation_zero k)
lemma rule_820 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.rule_820 (a k) (relation_zero k)
lemma rule_821 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.rule_821 (a k) (relation_zero k)
lemma rule_822 : word (a k) [13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_822 (a k) (relation_zero k)
lemma rule_823 : word (a k) [17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_823 (a k) (relation_zero k)
lemma rule_824 : word (a k) [63, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_824 (a k) (relation_zero k)
lemma rule_825 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_825 (a k) (relation_zero k)
lemma rule_826 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_826 (a k) (relation_zero k)
lemma rule_827 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_827 (a k) (relation_zero k)
lemma rule_828 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.rule_828 (a k) (relation_zero k)
lemma rule_829 : (-word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_829 (a k) (relation_zero k)
lemma rule_830 : (-word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]) + word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_830 (a k) (relation_zero k)
lemma rule_831 : (-word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9]) + word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_831 (a k) (relation_zero k)
lemma rule_832 : word (a k) [3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.rule_832 (a k) (relation_zero k)
lemma rule_833 : word (a k) [37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_833 (a k) (relation_zero k)
lemma rule_834 : word (a k) [66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_834 (a k) (relation_zero k)
lemma rule_835 : word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.rule_835 (a k) (relation_zero k)
lemma rule_836 : word (a k) [12, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  exact Universal.rule_836 (a k) (relation_zero k)
lemma rule_837 : word (a k) [61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  exact Universal.rule_837 (a k) (relation_zero k)
lemma rule_838 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_838 (a k) (relation_zero k)
lemma rule_839 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_839 (a k) (relation_zero k)
lemma rule_840 : (-word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19]) + word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_840 (a k) (relation_zero k)
lemma rule_841 : (-word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_841 (a k) (relation_zero k)
lemma rule_842 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.rule_842 (a k) (relation_zero k)
lemma rule_843 : word (a k) [41, 43, 48, 51, 64, 36, 71, 72, 38, 28, 14] + word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18]=0 := by
  exact Universal.rule_843 (a k) (relation_zero k)
lemma rule_844 : word (a k) [55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  exact Universal.rule_844 (a k) (relation_zero k)
lemma rule_845 : (-word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) + word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  exact Universal.rule_845 (a k) (relation_zero k)
lemma rule_846 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 54]=0 := by
  exact Universal.rule_846 (a k) (relation_zero k)
lemma rule_847 : word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69] + word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  exact Universal.rule_847 (a k) (relation_zero k)
lemma rule_848 : (-word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word (a k) [35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  exact Universal.rule_848 (a k) (relation_zero k)
lemma rule_849 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24] + word (a k) [52, 41, 43, 48, 51, 64, 36, 71, 72, 38, 29]=0 := by
  exact Universal.rule_849 (a k) (relation_zero k)
lemma rule_850 : (-word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43]) + word (a k) [10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 46]=0 := by
  exact Universal.rule_850 (a k) (relation_zero k)
lemma rule_851 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48] + (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59])=0 := by
  exact Universal.rule_851 (a k) (relation_zero k)
lemma rule_852 : word (a k) [11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6] + (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47])=0 := by
  exact Universal.rule_852 (a k) (relation_zero k)
lemma rule_853 : word (a k) [26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7] + (-word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  exact Universal.rule_853 (a k) (relation_zero k)
lemma rule_854 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.rule_854 (a k) (relation_zero k)
lemma rule_855 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17] + (-word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  exact Universal.rule_855 (a k) (relation_zero k)
lemma rule_856 : (-word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_856 (a k) (relation_zero k)
lemma rule_857 : (-word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_857 (a k) (relation_zero k)
lemma rule_858 : (-word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_858 (a k) (relation_zero k)
lemma rule_859 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 41] + (-word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56])=0 := by
  exact Universal.rule_859 (a k) (relation_zero k)
lemma rule_860 : word (a k) [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_860 (a k) (relation_zero k)
lemma rule_861 : (-word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27]) + word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 44]=0 := by
  exact Universal.rule_861 (a k) (relation_zero k)
lemma rule_862 : word (a k) [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_862 (a k) (relation_zero k)
lemma rule_863 : word (a k) [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_863 (a k) (relation_zero k)
lemma rule_864 : (-word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_864 (a k) (relation_zero k)
lemma rule_865 : (-word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) + word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  exact Universal.rule_865 (a k) (relation_zero k)
lemma rule_866 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 16, 57, 5] + (-word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34])=0 := by
  exact Universal.rule_866 (a k) (relation_zero k)
lemma rule_867 : (-word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_867 (a k) (relation_zero k)
lemma rule_868 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_868 (a k) (relation_zero k)
lemma rule_869 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_869 (a k) (relation_zero k)
lemma rule_870 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_870 (a k) (relation_zero k)
lemma rule_871 : word (a k) [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_871 (a k) (relation_zero k)
lemma rule_872 : word (a k) [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.rule_872 (a k) (relation_zero k)
lemma rule_873 : word (a k) [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_873 (a k) (relation_zero k)
lemma rule_874 : (-word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) + word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  exact Universal.rule_874 (a k) (relation_zero k)
lemma rule_875 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  exact Universal.rule_875 (a k) (relation_zero k)
lemma rule_876 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25] + word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 68, 40]=0 := by
  exact Universal.rule_876 (a k) (relation_zero k)
lemma rule_877 : (-word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  exact Universal.rule_877 (a k) (relation_zero k)
lemma rule_878 : (-word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  exact Universal.rule_878 (a k) (relation_zero k)
lemma rule_879 : (-word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  exact Universal.rule_879 (a k) (relation_zero k)
lemma rule_880 : (-word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  exact Universal.rule_880 (a k) (relation_zero k)
lemma rule_881 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  exact Universal.rule_881 (a k) (relation_zero k)
lemma rule_882 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  exact Universal.rule_882 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
