import N6Rules12
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_959 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_905 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_960 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_906 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_961 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_907 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_962 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_822 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_945 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_963 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_823 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_946 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_964 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_824 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_947 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_965 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_918 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_966 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_919 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_967 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_657 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_794 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_840 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_912 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_968 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 34, 63, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_658 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_795 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_841 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_913 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_969 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_948 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_970 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_949 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_971 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_868 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_937 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_972 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_869 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_938 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_973 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_870 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_939 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_974 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_975 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_976 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_977 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_978 : word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_940 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_979 : word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_941 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_980 : word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_942 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_981 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_940 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_982 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_941 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_983 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_942 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_984 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_936 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_985 : (-word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_986 : (-word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]) + word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_987 : word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_988 : word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_989 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_990 : word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_956 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_991 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_992 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_993 : (-word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_994 : (-word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_995 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55]) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_996 : word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_929 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_997 : word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_930 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_998 : (-word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) + word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_999 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69] + word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_950 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1000 : (-word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_957 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1001 : (-word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_958 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1002 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48] + (-word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59])=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_943 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1003 : word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6] + (-word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47])=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42]) (defining_35 v H)
  have h1 := congrArg (fun x : A => word v [47] * x) (rule_931 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1004 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7] + (-word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [50] * x) (rule_932 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1005 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1006 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17] + (-word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_944 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1007 : (-word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_912 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1008 : (-word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_913 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1009 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_894 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_937 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1010 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_895 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_938 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1011 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_896 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_939 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1012 : (-word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_908 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1013 : (-word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) + word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_924 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1014 : (-word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_909 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1015 : (-word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_910 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1016 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_920 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_922 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1017 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_921 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_923 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1018 : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_886 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_900 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_1019 : (-word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) + word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_927 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1020 : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_887 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_901 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_1021 : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_888 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_902 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_1022 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_903 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1023 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_904 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1024 : (-word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_935 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1025 : (-word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_928 v H)
  have h2 := congrArg (fun x : A => word v [73] * x) (rule_917 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1026 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_955 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_959 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_959 (a k) (relation_zero k)
lemma rule_960 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_960 (a k) (relation_zero k)
lemma rule_961 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_961 (a k) (relation_zero k)
lemma rule_962 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_962 (a k) (relation_zero k)
lemma rule_963 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_963 (a k) (relation_zero k)
lemma rule_964 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_964 (a k) (relation_zero k)
lemma rule_965 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.rule_965 (a k) (relation_zero k)
lemma rule_966 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.rule_966 (a k) (relation_zero k)
lemma rule_967 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_967 (a k) (relation_zero k)
lemma rule_968 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_968 (a k) (relation_zero k)
lemma rule_969 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_969 (a k) (relation_zero k)
lemma rule_970 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_970 (a k) (relation_zero k)
lemma rule_971 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_971 (a k) (relation_zero k)
lemma rule_972 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_972 (a k) (relation_zero k)
lemma rule_973 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_973 (a k) (relation_zero k)
lemma rule_974 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_974 (a k) (relation_zero k)
lemma rule_975 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_975 (a k) (relation_zero k)
lemma rule_976 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_976 (a k) (relation_zero k)
lemma rule_977 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.rule_977 (a k) (relation_zero k)
lemma rule_978 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_978 (a k) (relation_zero k)
lemma rule_979 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_979 (a k) (relation_zero k)
lemma rule_980 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_980 (a k) (relation_zero k)
lemma rule_981 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_981 (a k) (relation_zero k)
lemma rule_982 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_982 (a k) (relation_zero k)
lemma rule_983 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_983 (a k) (relation_zero k)
lemma rule_984 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.rule_984 (a k) (relation_zero k)
lemma rule_985 : (-word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_985 (a k) (relation_zero k)
lemma rule_986 : (-word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]) + word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_986 (a k) (relation_zero k)
lemma rule_987 : word (a k) [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_987 (a k) (relation_zero k)
lemma rule_988 : word (a k) [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.rule_988 (a k) (relation_zero k)
lemma rule_989 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.rule_989 (a k) (relation_zero k)
lemma rule_990 : word (a k) [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  exact Universal.rule_990 (a k) (relation_zero k)
lemma rule_991 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_991 (a k) (relation_zero k)
lemma rule_992 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_992 (a k) (relation_zero k)
lemma rule_993 : (-word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_993 (a k) (relation_zero k)
lemma rule_994 : (-word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_994 (a k) (relation_zero k)
lemma rule_995 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.rule_995 (a k) (relation_zero k)
lemma rule_996 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  exact Universal.rule_996 (a k) (relation_zero k)
lemma rule_997 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  exact Universal.rule_997 (a k) (relation_zero k)
lemma rule_998 : (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) + word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  exact Universal.rule_998 (a k) (relation_zero k)
lemma rule_999 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69] + word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  exact Universal.rule_999 (a k) (relation_zero k)
lemma rule_1000 : (-word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  exact Universal.rule_1000 (a k) (relation_zero k)
lemma rule_1001 : (-word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  exact Universal.rule_1001 (a k) (relation_zero k)
lemma rule_1002 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 48] + (-word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59])=0 := by
  exact Universal.rule_1002 (a k) (relation_zero k)
lemma rule_1003 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45, 6] + (-word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47])=0 := by
  exact Universal.rule_1003 (a k) (relation_zero k)
lemma rule_1004 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7] + (-word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  exact Universal.rule_1004 (a k) (relation_zero k)
lemma rule_1005 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.rule_1005 (a k) (relation_zero k)
lemma rule_1006 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17] + (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  exact Universal.rule_1006 (a k) (relation_zero k)
lemma rule_1007 : (-word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_1007 (a k) (relation_zero k)
lemma rule_1008 : (-word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_1008 (a k) (relation_zero k)
lemma rule_1009 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_1009 (a k) (relation_zero k)
lemma rule_1010 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_1010 (a k) (relation_zero k)
lemma rule_1011 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_1011 (a k) (relation_zero k)
lemma rule_1012 : (-word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_1012 (a k) (relation_zero k)
lemma rule_1013 : (-word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) + word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  exact Universal.rule_1013 (a k) (relation_zero k)
lemma rule_1014 : (-word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_1014 (a k) (relation_zero k)
lemma rule_1015 : (-word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_1015 (a k) (relation_zero k)
lemma rule_1016 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_1016 (a k) (relation_zero k)
lemma rule_1017 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60, 4] + (-word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_1017 (a k) (relation_zero k)
lemma rule_1018 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_1018 (a k) (relation_zero k)
lemma rule_1019 : (-word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) + word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  exact Universal.rule_1019 (a k) (relation_zero k)
lemma rule_1020 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.rule_1020 (a k) (relation_zero k)
lemma rule_1021 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_1021 (a k) (relation_zero k)
lemma rule_1022 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  exact Universal.rule_1022 (a k) (relation_zero k)
lemma rule_1023 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  exact Universal.rule_1023 (a k) (relation_zero k)
lemma rule_1024 : (-word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  exact Universal.rule_1024 (a k) (relation_zero k)
lemma rule_1025 : (-word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  exact Universal.rule_1025 (a k) (relation_zero k)
lemma rule_1026 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  exact Universal.rule_1026 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
