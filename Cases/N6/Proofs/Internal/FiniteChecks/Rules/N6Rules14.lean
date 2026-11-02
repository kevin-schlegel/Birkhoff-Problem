import N6Rules13
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_1027 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_978 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1028 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_979 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1029 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_980 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1030 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_905 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_1012 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_1031 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_906 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_1014 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_1032 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_907 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_1015 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_1033 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_990 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1034 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 34, 63, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_750 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_875 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_922 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_985 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_1035 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_751 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_876 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_923 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_986 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_1036 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_1016 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1037 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_1017 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1038 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_948 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_1007 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_1039 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_949 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_1008 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_1040 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1041 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1042 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1043 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1044 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_1009 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1045 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_1010 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1046 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_1011 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1047 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_1009 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1048 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_1010 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1049 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_1011 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1050 : word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_1006 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1051 : (-word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1052 : (-word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1053 : word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1054 : word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1055 : word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1056 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1057 : word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_1025 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1058 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1059 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1060 : (-word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1061 : (-word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1062 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_1000 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1063 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_1001 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1064 : (-word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) + word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1065 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69] + word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_1019 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1066 : (-word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_1026 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1067 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7] + (-word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [50] * x) (rule_1002 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1068 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1069 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17] + (-word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_1013 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1070 : (-word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_985 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1071 : (-word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_986 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1072 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_969 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_1007 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1073 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_970 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_1008 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1074 : (-word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_981 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1075 : (-word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_982 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1076 : (-word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_983 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1077 : (-word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) + word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_995 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1078 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_991 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_993 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1079 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_992 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_994 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1080 : (-word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) + word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_998 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1081 : word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_962 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_974 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_1082 : word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_963 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_975 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_1083 : word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_964 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_976 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_1084 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_977 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1085 : (-word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_1005 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1086 : (-word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_999 v H)
  have h2 := congrArg (fun x : A => word v [73] * x) (rule_989 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1087 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_1024 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_1027 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_1027 (a k) (relation_zero k)
lemma rule_1028 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_1028 (a k) (relation_zero k)
lemma rule_1029 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_1029 (a k) (relation_zero k)
lemma rule_1030 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_1030 (a k) (relation_zero k)
lemma rule_1031 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_1031 (a k) (relation_zero k)
lemma rule_1032 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_1032 (a k) (relation_zero k)
lemma rule_1033 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.rule_1033 (a k) (relation_zero k)
lemma rule_1034 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_1034 (a k) (relation_zero k)
lemma rule_1035 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_1035 (a k) (relation_zero k)
lemma rule_1036 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_1036 (a k) (relation_zero k)
lemma rule_1037 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_1037 (a k) (relation_zero k)
lemma rule_1038 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_1038 (a k) (relation_zero k)
lemma rule_1039 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_1039 (a k) (relation_zero k)
lemma rule_1040 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_1040 (a k) (relation_zero k)
lemma rule_1041 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_1041 (a k) (relation_zero k)
lemma rule_1042 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_1042 (a k) (relation_zero k)
lemma rule_1043 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.rule_1043 (a k) (relation_zero k)
lemma rule_1044 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_1044 (a k) (relation_zero k)
lemma rule_1045 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_1045 (a k) (relation_zero k)
lemma rule_1046 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_1046 (a k) (relation_zero k)
lemma rule_1047 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_1047 (a k) (relation_zero k)
lemma rule_1048 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_1048 (a k) (relation_zero k)
lemma rule_1049 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_1049 (a k) (relation_zero k)
lemma rule_1050 : word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.rule_1050 (a k) (relation_zero k)
lemma rule_1051 : (-word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_1051 (a k) (relation_zero k)
lemma rule_1052 : (-word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_1052 (a k) (relation_zero k)
lemma rule_1053 : word (a k) [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_1053 (a k) (relation_zero k)
lemma rule_1054 : word (a k) [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.rule_1054 (a k) (relation_zero k)
lemma rule_1055 : word (a k) [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_1055 (a k) (relation_zero k)
lemma rule_1056 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.rule_1056 (a k) (relation_zero k)
lemma rule_1057 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  exact Universal.rule_1057 (a k) (relation_zero k)
lemma rule_1058 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_1058 (a k) (relation_zero k)
lemma rule_1059 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_1059 (a k) (relation_zero k)
lemma rule_1060 : (-word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_1060 (a k) (relation_zero k)
lemma rule_1061 : (-word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_1061 (a k) (relation_zero k)
lemma rule_1062 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  exact Universal.rule_1062 (a k) (relation_zero k)
lemma rule_1063 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  exact Universal.rule_1063 (a k) (relation_zero k)
lemma rule_1064 : (-word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) + word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 65]=0 := by
  exact Universal.rule_1064 (a k) (relation_zero k)
lemma rule_1065 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69] + word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  exact Universal.rule_1065 (a k) (relation_zero k)
lemma rule_1066 : (-word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  exact Universal.rule_1066 (a k) (relation_zero k)
lemma rule_1067 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47, 7] + (-word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50])=0 := by
  exact Universal.rule_1067 (a k) (relation_zero k)
lemma rule_1068 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.rule_1068 (a k) (relation_zero k)
lemma rule_1069 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50, 17] + (-word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63])=0 := by
  exact Universal.rule_1069 (a k) (relation_zero k)
lemma rule_1070 : (-word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_1070 (a k) (relation_zero k)
lemma rule_1071 : (-word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_1071 (a k) (relation_zero k)
lemma rule_1072 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_1072 (a k) (relation_zero k)
lemma rule_1073 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_1073 (a k) (relation_zero k)
lemma rule_1074 : (-word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_1074 (a k) (relation_zero k)
lemma rule_1075 : (-word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_1075 (a k) (relation_zero k)
lemma rule_1076 : (-word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_1076 (a k) (relation_zero k)
lemma rule_1077 : (-word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) + word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 51]=0 := by
  exact Universal.rule_1077 (a k) (relation_zero k)
lemma rule_1078 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_1078 (a k) (relation_zero k)
lemma rule_1079 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_1079 (a k) (relation_zero k)
lemma rule_1080 : (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) + word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  exact Universal.rule_1080 (a k) (relation_zero k)
lemma rule_1081 : word (a k) [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_1081 (a k) (relation_zero k)
lemma rule_1082 : word (a k) [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_1082 (a k) (relation_zero k)
lemma rule_1083 : word (a k) [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_1083 (a k) (relation_zero k)
lemma rule_1084 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  exact Universal.rule_1084 (a k) (relation_zero k)
lemma rule_1085 : (-word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  exact Universal.rule_1085 (a k) (relation_zero k)
lemma rule_1086 : (-word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  exact Universal.rule_1086 (a k) (relation_zero k)
lemma rule_1087 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  exact Universal.rule_1087 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
