import N6Rules15
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_1142 : word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_1105 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1143 : word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_1106 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1144 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_1044 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_1129 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_1145 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_1045 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_1130 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_1146 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [34, 64] * x) (rule_1046 v H)
  have h2 := congrArg (fun x : A => word v [64] * x) (rule_1131 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_1147 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_1116 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1148 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_918 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_1022 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_1060 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_1110 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_1149 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 22]) (defining_3 v H)
  have h1 := congrArg (fun x : A => word v [40, 62, 52, 42] * x) (rule_919 v H)
  have h2 := congrArg (fun x : A => word v [62, 52, 42] * x) (rule_1023 v H)
  have h3 := congrArg (fun x : A => word v [52, 42] * x) (rule_1061 v H)
  have h4 := congrArg (fun x : A => word v [42] * x) (rule_1111 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (1) * h2 + (-1) * h3 + (-1) * h4
lemma rule_1150 : word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_1132 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1151 : word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_1133 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1152 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_1078 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_1125 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_1153 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_1079 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_1126 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_1154 : word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1155 : word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1156 : word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1157 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1158 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_1127 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1159 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_1128 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1160 : word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_1127 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1161 : word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_1128 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1162 : word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_1124 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1163 : (-word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1164 : word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1165 : word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1166 : word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1167 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1168 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_1140 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1169 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1170 : (-word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1171 : word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_1122 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1172 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69] + word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_1135 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_1173 : (-word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_1141 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1174 : word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1175 : (-word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_1110 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1176 : (-word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_1111 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1177 : word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_1097 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_1125 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1178 : word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_1098 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_1126 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1179 : (-word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_1107 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1180 : (-word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_1108 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1181 : word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_1117 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_1118 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1182 : word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_1091 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_1101 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_1183 : word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_1092 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_1102 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_1184 : word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_1093 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_1103 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_1185 : (-word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) + word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_1120 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_1186 : word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_1104 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1187 : (-word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_1123 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_1188 : (-word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_1121 v H)
  have h2 := congrArg (fun x : A => word v [73] * x) (rule_1115 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_1189 : word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_1139 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_1142 : word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_1142 (a k) (relation_zero k)
lemma rule_1143 : word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_1143 (a k) (relation_zero k)
lemma rule_1144 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_1144 (a k) (relation_zero k)
lemma rule_1145 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_1145 (a k) (relation_zero k)
lemma rule_1146 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_1146 (a k) (relation_zero k)
lemma rule_1147 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.rule_1147 (a k) (relation_zero k)
lemma rule_1148 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_1148 (a k) (relation_zero k)
lemma rule_1149 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_1149 (a k) (relation_zero k)
lemma rule_1150 : word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_1150 (a k) (relation_zero k)
lemma rule_1151 : word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_1151 (a k) (relation_zero k)
lemma rule_1152 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_1152 (a k) (relation_zero k)
lemma rule_1153 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_1153 (a k) (relation_zero k)
lemma rule_1154 : word (a k) [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_1154 (a k) (relation_zero k)
lemma rule_1155 : word (a k) [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_1155 (a k) (relation_zero k)
lemma rule_1156 : word (a k) [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_1156 (a k) (relation_zero k)
lemma rule_1157 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.rule_1157 (a k) (relation_zero k)
lemma rule_1158 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_1158 (a k) (relation_zero k)
lemma rule_1159 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15, 1] + (-word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_1159 (a k) (relation_zero k)
lemma rule_1160 : word (a k) [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_1160 (a k) (relation_zero k)
lemma rule_1161 : word (a k) [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_1161 (a k) (relation_zero k)
lemma rule_1162 : word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.rule_1162 (a k) (relation_zero k)
lemma rule_1163 : (-word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]) + word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_1163 (a k) (relation_zero k)
lemma rule_1164 : word (a k) [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_1164 (a k) (relation_zero k)
lemma rule_1165 : word (a k) [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_1165 (a k) (relation_zero k)
lemma rule_1166 : word (a k) [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_1166 (a k) (relation_zero k)
lemma rule_1167 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.rule_1167 (a k) (relation_zero k)
lemma rule_1168 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22, 3] + word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0 := by
  exact Universal.rule_1168 (a k) (relation_zero k)
lemma rule_1169 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_1169 (a k) (relation_zero k)
lemma rule_1170 : (-word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]) + word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_1170 (a k) (relation_zero k)
lemma rule_1171 : word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28, 14] + (-word (a k) [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18])=0 := by
  exact Universal.rule_1171 (a k) (relation_zero k)
lemma rule_1172 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 69] + word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69]=0 := by
  exact Universal.rule_1172 (a k) (relation_zero k)
lemma rule_1173 : (-word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]) + word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 29]=0 := by
  exact Universal.rule_1173 (a k) (relation_zero k)
lemma rule_1174 : word (a k) [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.rule_1174 (a k) (relation_zero k)
lemma rule_1175 : (-word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_1175 (a k) (relation_zero k)
lemma rule_1176 : (-word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]) + word (a k) [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_1176 (a k) (relation_zero k)
lemma rule_1177 : word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_1177 (a k) (relation_zero k)
lemma rule_1178 : word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 16] + (-word (a k) [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_1178 (a k) (relation_zero k)
lemma rule_1179 : (-word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_1179 (a k) (relation_zero k)
lemma rule_1180 : (-word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]) + word (a k) [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_1180 (a k) (relation_zero k)
lemma rule_1181 : word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60, 4] + (-word (a k) [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_1181 (a k) (relation_zero k)
lemma rule_1182 : word (a k) [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_1182 (a k) (relation_zero k)
lemma rule_1183 : word (a k) [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_1183 (a k) (relation_zero k)
lemma rule_1184 : word (a k) [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_1184 (a k) (relation_zero k)
lemma rule_1185 : (-word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]) + word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64, 36] + (-word (a k) [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49])=0 := by
  exact Universal.rule_1185 (a k) (relation_zero k)
lemma rule_1186 : word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] + word (a k) [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68, 40]=0 := by
  exact Universal.rule_1186 (a k) (relation_zero k)
lemma rule_1187 : (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 73]=0 := by
  exact Universal.rule_1187 (a k) (relation_zero k)
lemma rule_1188 : (-word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]) + word (a k) [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 23]=0 := by
  exact Universal.rule_1188 (a k) (relation_zero k)
lemma rule_1189 : word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 37] + (-word (a k) [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66])=0 := by
  exact Universal.rule_1189 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
