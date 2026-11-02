import N6Rules11
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_883 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_822 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_884 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_823 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_885 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_824 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_886 : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_735 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_864 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_887 : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22, 3, 40, 60, 4, 54, 15]) (defining_1 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_888 : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_737 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_867 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_889 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 34, 63, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_836 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_890 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 34, 63, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_837 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_891 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 34, 63, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_560 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_705 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_755 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_829 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_892 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_561 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_706 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_756 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_830 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_893 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_562 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_707 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_757 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_831 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_894 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_868 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_895 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_869 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_896 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_870 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_897 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_786 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_856 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_898 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_787 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_857 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_899 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_788 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_858 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_900 : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_901 : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22, 3, 40, 60, 4, 54, 16, 57]) (defining_7 v H)
  have h1 := congrArg (fun x : A => word v [65] * x) (rule_866 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_902 : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_903 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_904 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_905 : word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_860 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_906 : word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_862 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_907 : word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_863 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_908 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_860 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_909 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_862 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_910 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_863 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_911 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55, 27, 59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_855 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_912 : (-word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]) + word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_913 : (-word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_914 : word v [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 24, 18, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_915 : word v [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [22, 3, 40, 60, 4, 54, 15, 1, 34, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_916 : word v [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 24, 18, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_917 : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_918 : word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_878 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_919 : word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_880 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_920 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_921 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_922 : (-word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_923 : (-word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19]) + word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_924 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55]) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_925 : word v [35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_848 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_926 : word v [52, 41, 43, 48, 51, 64, 36, 71, 72, 38, 28, 14] + word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 48, 51, 64, 36, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_849 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_927 : (-word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) + word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_928 : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69] + word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_874 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_929 : (-word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_881 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_930 : (-word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_882 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_931 : (-word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43]) + word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 46]=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 52]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [43] * x) (rule_859 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_932 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48] + (-word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59])=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_861 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_933 : word v [10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6] + (-word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47])=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 62, 52, 42]) (defining_35 v H)
  have h1 := congrArg (fun x : A => word v [47] * x) (rule_850 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_934 : word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7] + (-word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 61, 35, 56, 43]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [50] * x) (rule_851 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_935 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_936 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17] + (-word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_865 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_937 : (-word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_829 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_938 : (-word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_830 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_939 : (-word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_831 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_940 : word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_812 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_856 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_941 : word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_813 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_857 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_942 : word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_814 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_858 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_943 : (-word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27]) + word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [16] * x) (rule_846 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_944 : (-word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) + word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_842 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_945 : (-word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_825 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_946 : (-word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_826 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_947 : (-word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_827 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_948 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_838 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_840 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_949 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_839 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_841 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_950 : (-word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) + word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_845 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_951 : word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_805 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_818 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_952 : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_806 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_819 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_953 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_820 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_954 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_821 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_955 : (-word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_854 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_956 : (-word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_847 v H)
  have h2 := congrArg (fun x : A => word v [73] * x) (rule_835 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_957 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_877 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_958 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_879 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_883 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_883 (a k) (relation_zero k)
lemma rule_884 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_884 (a k) (relation_zero k)
lemma rule_885 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_885 (a k) (relation_zero k)
lemma rule_886 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_886 (a k) (relation_zero k)
lemma rule_887 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.rule_887 (a k) (relation_zero k)
lemma rule_888 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_888 (a k) (relation_zero k)
lemma rule_889 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.rule_889 (a k) (relation_zero k)
lemma rule_890 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.rule_890 (a k) (relation_zero k)
lemma rule_891 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_891 (a k) (relation_zero k)
lemma rule_892 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_892 (a k) (relation_zero k)
lemma rule_893 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_893 (a k) (relation_zero k)
lemma rule_894 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_894 (a k) (relation_zero k)
lemma rule_895 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_895 (a k) (relation_zero k)
lemma rule_896 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_896 (a k) (relation_zero k)
lemma rule_897 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_897 (a k) (relation_zero k)
lemma rule_898 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_898 (a k) (relation_zero k)
lemma rule_899 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_899 (a k) (relation_zero k)
lemma rule_900 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_900 (a k) (relation_zero k)
lemma rule_901 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.rule_901 (a k) (relation_zero k)
lemma rule_902 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_902 (a k) (relation_zero k)
lemma rule_903 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.rule_903 (a k) (relation_zero k)
lemma rule_904 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.rule_904 (a k) (relation_zero k)
lemma rule_905 : word (a k) [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_905 (a k) (relation_zero k)
lemma rule_906 : word (a k) [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_906 (a k) (relation_zero k)
lemma rule_907 : word (a k) [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_907 (a k) (relation_zero k)
lemma rule_908 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_908 (a k) (relation_zero k)
lemma rule_909 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_909 (a k) (relation_zero k)
lemma rule_910 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_910 (a k) (relation_zero k)
lemma rule_911 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.rule_911 (a k) (relation_zero k)
lemma rule_912 : (-word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]) + word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_912 (a k) (relation_zero k)
lemma rule_913 : (-word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_913 (a k) (relation_zero k)
lemma rule_914 : word (a k) [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_914 (a k) (relation_zero k)
lemma rule_915 : word (a k) [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.rule_915 (a k) (relation_zero k)
lemma rule_916 : word (a k) [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_916 (a k) (relation_zero k)
lemma rule_917 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.rule_917 (a k) (relation_zero k)
lemma rule_918 : word (a k) [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  exact Universal.rule_918 (a k) (relation_zero k)
lemma rule_919 : word (a k) [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  exact Universal.rule_919 (a k) (relation_zero k)
lemma rule_920 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_920 (a k) (relation_zero k)
lemma rule_921 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_921 (a k) (relation_zero k)
lemma rule_922 : (-word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_922 (a k) (relation_zero k)
lemma rule_923 : (-word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19]) + word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_923 (a k) (relation_zero k)
lemma rule_924 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.rule_924 (a k) (relation_zero k)
lemma rule_925 : word (a k) [35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  exact Universal.rule_925 (a k) (relation_zero k)
lemma rule_926 : word (a k) [52, 41, 43, 48, 51, 64, 36, 71, 72, 38, 28, 14] + word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18]=0 := by
  exact Universal.rule_926 (a k) (relation_zero k)
lemma rule_927 : (-word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) + word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  exact Universal.rule_927 (a k) (relation_zero k)
lemma rule_928 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69] + word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  exact Universal.rule_928 (a k) (relation_zero k)
lemma rule_929 : (-word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  exact Universal.rule_929 (a k) (relation_zero k)
lemma rule_930 : (-word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  exact Universal.rule_930 (a k) (relation_zero k)
lemma rule_931 : (-word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43]) + word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 46]=0 := by
  exact Universal.rule_931 (a k) (relation_zero k)
lemma rule_932 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48] + (-word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59])=0 := by
  exact Universal.rule_932 (a k) (relation_zero k)
lemma rule_933 : word (a k) [10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6] + (-word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47])=0 := by
  exact Universal.rule_933 (a k) (relation_zero k)
lemma rule_934 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7] + (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  exact Universal.rule_934 (a k) (relation_zero k)
lemma rule_935 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.rule_935 (a k) (relation_zero k)
lemma rule_936 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17] + (-word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  exact Universal.rule_936 (a k) (relation_zero k)
lemma rule_937 : (-word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_937 (a k) (relation_zero k)
lemma rule_938 : (-word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_938 (a k) (relation_zero k)
lemma rule_939 : (-word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_939 (a k) (relation_zero k)
lemma rule_940 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_940 (a k) (relation_zero k)
lemma rule_941 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_941 (a k) (relation_zero k)
lemma rule_942 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_942 (a k) (relation_zero k)
lemma rule_943 : (-word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27]) + word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 44]=0 := by
  exact Universal.rule_943 (a k) (relation_zero k)
lemma rule_944 : (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) + word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  exact Universal.rule_944 (a k) (relation_zero k)
lemma rule_945 : (-word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_945 (a k) (relation_zero k)
lemma rule_946 : (-word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_946 (a k) (relation_zero k)
lemma rule_947 : (-word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_947 (a k) (relation_zero k)
lemma rule_948 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_948 (a k) (relation_zero k)
lemma rule_949 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_949 (a k) (relation_zero k)
lemma rule_950 : (-word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) + word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  exact Universal.rule_950 (a k) (relation_zero k)
lemma rule_951 : word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_951 (a k) (relation_zero k)
lemma rule_952 : word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.rule_952 (a k) (relation_zero k)
lemma rule_953 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  exact Universal.rule_953 (a k) (relation_zero k)
lemma rule_954 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  exact Universal.rule_954 (a k) (relation_zero k)
lemma rule_955 : (-word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  exact Universal.rule_955 (a k) (relation_zero k)
lemma rule_956 : (-word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  exact Universal.rule_956 (a k) (relation_zero k)
lemma rule_957 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  exact Universal.rule_957 (a k) (relation_zero k)
lemma rule_958 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  exact Universal.rule_958 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
