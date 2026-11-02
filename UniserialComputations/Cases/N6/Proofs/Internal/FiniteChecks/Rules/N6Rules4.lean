import N6Rules3
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_114 : word v [54, 15, 1, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [54, 15]) (defining_0 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_115 : word v [15, 1, 34, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [15]) (defining_1 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_116 : word v [70, 22, 3, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22]) (defining_2 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_117 : word v [24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_100 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_118 : word v [40, 60, 4, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 60]) (defining_4 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_119 : word v [60, 4, 56, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [60]) (defining_5 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_120 : word v [44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [44, 57]) (defining_6 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_121 : word v [15, 1, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [16, 57]) (defining_7 v H)
  have h1 := congrArg (fun x : A => word v [65] * x) (rule_97 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_122 : word v [44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_123 : word v [69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69]) (defining_8 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_124 : word v [21, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_125 : word v [49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_126 : word v [24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [24, 18]) (defining_11 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_127 : word v [28, 14, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [28, 14]) (defining_11 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_128 : (-word v [4, 54, 15, 1]) + word v [4, 54, 16, 58]=0 := by
  have h0 := congrArg (fun x : A => x * word v [4, 54]) (defining_12 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_129 : (-word v [53, 54, 15, 1]) + word v [53, 54, 16, 58]=0 := by
  have h0 := congrArg (fun x : A => x * word v [53, 54]) (defining_12 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_130 : word v [4, 54, 16, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [4, 54]) (defining_13 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_131 : word v [53, 54, 16, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [53, 54]) (defining_13 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_132 : word v [6, 7, 17, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7]) (defining_14 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_133 : word v [47, 7, 17, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7]) (defining_14 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_134 : (-word v [57, 5, 63, 20]) + word v [58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_91 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_135 : word v [29, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [29]) (defining_15 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_136 : (-word v [37, 24, 18, 9]) + word v [37, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_137 : (-word v [66, 24, 18, 9]) + word v [66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_138 : word v [5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_139 : word v [34, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [34, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_140 : word v [7, 17, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_141 : word v [34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_142 : word v [50, 17, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_143 : word v [36, 70, 23, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70]) (defining_19 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_144 : word v [21, 70, 22, 3] + (-word v [21, 69, 8, 68])=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_109 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_145 : word v [36, 70, 22, 3] + word v [36, 70, 23, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70]) (defining_20 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_146 : word v [8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_147 : word v [22, 3, 40, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [23, 66]) (defining_21 v H)
  have h1 := congrArg (fun x : A => word v [61] * x) (rule_107 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_148 : word v [72, 37, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_149 : (-word v [8, 66, 24, 19]) + word v [8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_150 : word v [23, 66, 24, 19] + (-word v [22, 3, 40, 62])=0 := by
  have h0 := congrArg (fun x : A => x * word v [23, 66]) (defining_22 v H)
  have h1 := congrArg (fun x : A => word v [62] * x) (rule_107 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_151 : (-word v [72, 37, 24, 19]) + word v [72, 37, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_152 : word v [10, 11, 26, 30]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11]) (defining_23 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_153 : word v [35, 55, 27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55]) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_154 : word v [53, 54, 16, 57] + (-word v [52, 41, 44, 57])=0 := by
  have h0 := congrArg (fun x : A => x * word v [53, 55]) (defining_24 v H)
  have h1 := congrArg (fun x : A => word v [57] * x) (rule_96 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_155 : word v [72, 38, 28, 14] + (-word v [72, 37, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_78 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_156 : word v [11, 26, 31, 72]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26]) (defining_26 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_157 : word v [73, 67, 32, 60]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67]) (defining_27 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_158 : (-word v [27, 58, 33, 13]) + word v [27, 58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_159 : word v [44, 58, 33, 13] + (-word v [43, 48, 51, 65])=0 := by
  have h0 := congrArg (fun x : A => x * word v [44, 58]) (defining_28 v H)
  have h1 := congrArg (fun x : A => word v [65] * x) (rule_99 v H)
  have h2 := congrArg (fun x : A => word v [] * x) (rule_122 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2
lemma rule_160 : word v [32, 61, 35, 54]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61]) (defining_29 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_161 : word v [39, 12, 35, 54]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12]) (defining_29 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_162 : word v [34, 63, 21, 69] + word v [33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_104 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_163 : word v [51, 64, 36, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [51, 64]) (defining_30 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_164 : (-word v [69, 8, 66, 24]) + (-word v [70, 23, 66, 24]) + word v [71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_113 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_165 : word v [73, 68, 39, 12] + (-word v [73, 67, 32, 61])=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 68]) (defining_32 v H)
  have h1 := congrArg (fun x : A => word v [61] * x) (rule_108 v H)
  have h2 := congrArg (fun x : A => word v [] * x) (rule_148 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (-1) * h2
lemma rule_166 : word v [14, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [14, 9]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [46] * x) (rule_50 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_167 : word v [18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [18, 9]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [46] * x) (rule_51 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_168 : (-word v [61, 35, 56, 43]) + word v [62, 52, 42, 46]=0 := by
  have h0 := congrArg (fun x : A => x * word v [62, 52]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [43] * x) (rule_93 v H)
  have h2 := congrArg (fun x : A => word v [] * x) (rule_119 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (1) * h2
lemma rule_169 : word v [9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [9, 41]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [48] * x) (rule_81 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_170 : word v [35, 56, 43, 48] + (-word v [35, 55, 27, 59])=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 56]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_95 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_171 : (-word v [52, 41, 43, 48]) + word v [52, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41]) (defining_34 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_172 : word v [52, 42, 45, 6] + (-word v [52, 41, 43, 47])=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 42]) (defining_35 v H)
  have h1 := congrArg (fun x : A => word v [47] * x) (rule_82 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_173 : (-word v [41, 43, 47, 7]) + word v [41, 43, 48, 50]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43]) (defining_36 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_174 : word v [56, 43, 47, 7] + (-word v [55, 27, 59, 50])=0 := by
  have h0 := congrArg (fun x : A => x * word v [56, 43]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [50] * x) (rule_84 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_175 : word v [33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_176 : (-word v [50, 17, 21, 70]) + word v [51, 64, 36, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [51, 65]) (defining_37 v H)
  have h1 := congrArg (fun x : A => word v [70] * x) (rule_105 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_177 : word v [27, 59, 50, 17] + (-word v [27, 58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_98 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_178 : (-word v [43, 47, 7, 17]) + word v [43, 48, 51, 63]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 48]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [17] * x) (rule_86 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_179 : (-word v [45, 6, 7, 17]) + word v [46, 48, 51, 63]=0 := by
  have h0 := congrArg (fun x : A => x * word v [46, 48]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [17] * x) (rule_87 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_180 : (-word v [24, 18, 9, 41]) + word v [24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_57 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_181 : (-word v [28, 14, 9, 41]) + word v [29, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [29, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_58 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_182 : word v [32, 62, 52, 41] + (-word v [32, 61, 35, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_101 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_183 : word v [40, 62, 52, 41] + (-word v [40, 60, 4, 56]) + (-word v [39, 12, 35, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_102 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_184 : (-word v [12, 35, 55, 27]) + word v [12, 35, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [16] * x) (rule_75 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_185 : word v [19, 53, 54, 16] + (-word v [18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_56 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_92 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_186 : (-word v [60, 4, 54, 16]) + word v [60, 4, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [60, 4]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_44 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_187 : (-word v [61, 35, 55, 27]) + word v [61, 35, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [16] * x) (rule_76 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_188 : (-word v [41, 44, 57, 5]) + word v [41, 44, 58, 34] + (-word v [41, 43, 48, 51])=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_83 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_189 : word v [54, 16, 57, 5] + (-word v [54, 15, 1, 34])=0 := by
  have h0 := congrArg (fun x : A => x * word v [54, 16]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [34] * x) (rule_52 v H)
  have h2 := congrArg (fun x : A => word v [51] * x) (rule_53 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_190 : (-word v [55, 27, 58, 34]) + word v [55, 27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_69 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_191 : (-word v [3, 40, 60, 4]) + word v [3, 40, 62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v [3, 40]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_79 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_192 : word v [37, 25, 60, 4] + (-word v [37, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_64 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_66 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_193 : word v [66, 25, 60, 4] + (-word v [66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_65 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_67 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_194 : (-word v [67, 32, 61, 35]) + word v [67, 32, 62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [4] * x) (rule_72 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_195 : word v [1, 34, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [1, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_42 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_73 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_196 : word v [47, 7, 17, 21] + (-word v [48, 51, 64, 36]) + word v [48, 51, 65, 49]=0 := by
  have h0 := congrArg (fun x : A => x * word v [48, 51]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [21] * x) (rule_90 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_197 : word v [57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_46 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_47 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_198 : (-word v [58, 34, 63, 21]) + word v [58, 34, 64, 36] + (-word v [58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_74 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_199 : (-word v [31, 73, 67, 32]) + word v [31, 73, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [25] * x) (rule_112 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_200 : word v [69, 8, 66, 25] + word v [69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_49 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_201 : word v [70, 23, 66, 25] + (-word v [70, 22, 3, 40])=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 23]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_62 v H)
  have h2 := congrArg (fun x : A => word v [40] * x) (rule_63 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_202 : (-word v [13, 49, 69, 8]) + word v [13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_88 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_203 : word v [17, 21, 69, 8] + word v [17, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [73] * x) (rule_60 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_204 : word v [63, 21, 69, 8] + word v [63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [73] * x) (rule_61 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_205 : word v [64, 36, 71, 73] + word v [63, 21, 69, 8]=0 := by
  have h0 := congrArg (fun x : A => x * word v [64, 36]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_77 v H)
  have h2 := congrArg (fun x : A => word v [23] * x) (rule_89 v H)
  have h3 := congrArg (fun x : A => word v [] * x) (rule_204 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (1) * h2 + (1) * h3
lemma rule_206 : word v [26, 31, 73, 66]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [37] * x) (rule_71 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_207 : word v [36, 71, 72, 37] + (-word v [36, 70, 23, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_110 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_208 : word v [49, 71, 72, 37] + (-word v [49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_111 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_114 : word (a k) [54, 15, 1, 33]=0 := by
  exact Universal.rule_114 (a k) (relation_zero k)
lemma rule_115 : word (a k) [15, 1, 34, 64]=0 := by
  exact Universal.rule_115 (a k) (relation_zero k)
lemma rule_116 : word (a k) [70, 22, 3, 39]=0 := by
  exact Universal.rule_116 (a k) (relation_zero k)
lemma rule_117 : word (a k) [24, 19, 53, 55]=0 := by
  exact Universal.rule_117 (a k) (relation_zero k)
lemma rule_118 : word (a k) [40, 60, 4, 55]=0 := by
  exact Universal.rule_118 (a k) (relation_zero k)
lemma rule_119 : word (a k) [60, 4, 56, 43]=0 := by
  exact Universal.rule_119 (a k) (relation_zero k)
lemma rule_120 : word (a k) [44, 57, 5, 64]=0 := by
  exact Universal.rule_120 (a k) (relation_zero k)
lemma rule_121 : word (a k) [15, 1, 34, 65]=0 := by
  exact Universal.rule_121 (a k) (relation_zero k)
lemma rule_122 : word (a k) [44, 57, 5, 65]=0 := by
  exact Universal.rule_122 (a k) (relation_zero k)
lemma rule_123 : word (a k) [69, 8, 68, 39]=0 := by
  exact Universal.rule_123 (a k) (relation_zero k)
lemma rule_124 : word (a k) [21, 69, 8, 67]=0 := by
  exact Universal.rule_124 (a k) (relation_zero k)
lemma rule_125 : word (a k) [49, 69, 8, 67]=0 := by
  exact Universal.rule_125 (a k) (relation_zero k)
lemma rule_126 : word (a k) [24, 18, 9, 42]=0 := by
  exact Universal.rule_126 (a k) (relation_zero k)
lemma rule_127 : word (a k) [28, 14, 9, 42]=0 := by
  exact Universal.rule_127 (a k) (relation_zero k)
lemma rule_128 : (-word (a k) [4, 54, 15, 1]) + word (a k) [4, 54, 16, 58]=0 := by
  exact Universal.rule_128 (a k) (relation_zero k)
lemma rule_129 : (-word (a k) [53, 54, 15, 1]) + word (a k) [53, 54, 16, 58]=0 := by
  exact Universal.rule_129 (a k) (relation_zero k)
lemma rule_130 : word (a k) [4, 54, 16, 59]=0 := by
  exact Universal.rule_130 (a k) (relation_zero k)
lemma rule_131 : word (a k) [53, 54, 16, 59]=0 := by
  exact Universal.rule_131 (a k) (relation_zero k)
lemma rule_132 : word (a k) [6, 7, 17, 20]=0 := by
  exact Universal.rule_132 (a k) (relation_zero k)
lemma rule_133 : word (a k) [47, 7, 17, 20]=0 := by
  exact Universal.rule_133 (a k) (relation_zero k)
lemma rule_134 : (-word (a k) [57, 5, 63, 20]) + word (a k) [58, 34, 63, 20]=0 := by
  exact Universal.rule_134 (a k) (relation_zero k)
lemma rule_135 : word (a k) [29, 19, 53, 55]=0 := by
  exact Universal.rule_135 (a k) (relation_zero k)
lemma rule_136 : (-word (a k) [37, 24, 18, 9]) + word (a k) [37, 24, 19, 52]=0 := by
  exact Universal.rule_136 (a k) (relation_zero k)
lemma rule_137 : (-word (a k) [66, 24, 18, 9]) + word (a k) [66, 24, 19, 52]=0 := by
  exact Universal.rule_137 (a k) (relation_zero k)
lemma rule_138 : word (a k) [5, 63, 20, 31]=0 := by
  exact Universal.rule_138 (a k) (relation_zero k)
lemma rule_139 : word (a k) [34, 63, 20, 31]=0 := by
  exact Universal.rule_139 (a k) (relation_zero k)
lemma rule_140 : word (a k) [7, 17, 21, 71]=0 := by
  exact Universal.rule_140 (a k) (relation_zero k)
lemma rule_141 : word (a k) [34, 63, 21, 71]=0 := by
  exact Universal.rule_141 (a k) (relation_zero k)
lemma rule_142 : word (a k) [50, 17, 21, 71]=0 := by
  exact Universal.rule_142 (a k) (relation_zero k)
lemma rule_143 : word (a k) [36, 70, 23, 67]=0 := by
  exact Universal.rule_143 (a k) (relation_zero k)
lemma rule_144 : word (a k) [21, 70, 22, 3] + (-word (a k) [21, 69, 8, 68])=0 := by
  exact Universal.rule_144 (a k) (relation_zero k)
lemma rule_145 : word (a k) [36, 70, 22, 3] + word (a k) [36, 70, 23, 68]=0 := by
  exact Universal.rule_145 (a k) (relation_zero k)
lemma rule_146 : word (a k) [8, 66, 25, 61]=0 := by
  exact Universal.rule_146 (a k) (relation_zero k)
lemma rule_147 : word (a k) [22, 3, 40, 61]=0 := by
  exact Universal.rule_147 (a k) (relation_zero k)
lemma rule_148 : word (a k) [72, 37, 25, 61]=0 := by
  exact Universal.rule_148 (a k) (relation_zero k)
lemma rule_149 : (-word (a k) [8, 66, 24, 19]) + word (a k) [8, 66, 25, 62]=0 := by
  exact Universal.rule_149 (a k) (relation_zero k)
lemma rule_150 : word (a k) [23, 66, 24, 19] + (-word (a k) [22, 3, 40, 62])=0 := by
  exact Universal.rule_150 (a k) (relation_zero k)
lemma rule_151 : (-word (a k) [72, 37, 24, 19]) + word (a k) [72, 37, 25, 62]=0 := by
  exact Universal.rule_151 (a k) (relation_zero k)
lemma rule_152 : word (a k) [10, 11, 26, 30]=0 := by
  exact Universal.rule_152 (a k) (relation_zero k)
lemma rule_153 : word (a k) [35, 55, 27, 57]=0 := by
  exact Universal.rule_153 (a k) (relation_zero k)
lemma rule_154 : word (a k) [53, 54, 16, 57] + (-word (a k) [52, 41, 44, 57])=0 := by
  exact Universal.rule_154 (a k) (relation_zero k)
lemma rule_155 : word (a k) [72, 38, 28, 14] + (-word (a k) [72, 37, 24, 18])=0 := by
  exact Universal.rule_155 (a k) (relation_zero k)
lemma rule_156 : word (a k) [11, 26, 31, 72]=0 := by
  exact Universal.rule_156 (a k) (relation_zero k)
lemma rule_157 : word (a k) [73, 67, 32, 60]=0 := by
  exact Universal.rule_157 (a k) (relation_zero k)
lemma rule_158 : (-word (a k) [27, 58, 33, 13]) + word (a k) [27, 58, 34, 65]=0 := by
  exact Universal.rule_158 (a k) (relation_zero k)
lemma rule_159 : word (a k) [44, 58, 33, 13] + (-word (a k) [43, 48, 51, 65])=0 := by
  exact Universal.rule_159 (a k) (relation_zero k)
lemma rule_160 : word (a k) [32, 61, 35, 54]=0 := by
  exact Universal.rule_160 (a k) (relation_zero k)
lemma rule_161 : word (a k) [39, 12, 35, 54]=0 := by
  exact Universal.rule_161 (a k) (relation_zero k)
lemma rule_162 : word (a k) [34, 63, 21, 69] + word (a k) [33, 13, 49, 69]=0 := by
  exact Universal.rule_162 (a k) (relation_zero k)
lemma rule_163 : word (a k) [51, 64, 36, 69]=0 := by
  exact Universal.rule_163 (a k) (relation_zero k)
lemma rule_164 : (-word (a k) [69, 8, 66, 24]) + (-word (a k) [70, 23, 66, 24]) + word (a k) [71, 72, 38, 29]=0 := by
  exact Universal.rule_164 (a k) (relation_zero k)
lemma rule_165 : word (a k) [73, 68, 39, 12] + (-word (a k) [73, 67, 32, 61])=0 := by
  exact Universal.rule_165 (a k) (relation_zero k)
lemma rule_166 : word (a k) [14, 9, 41, 43]=0 := by
  exact Universal.rule_166 (a k) (relation_zero k)
lemma rule_167 : word (a k) [18, 9, 41, 43]=0 := by
  exact Universal.rule_167 (a k) (relation_zero k)
lemma rule_168 : (-word (a k) [61, 35, 56, 43]) + word (a k) [62, 52, 42, 46]=0 := by
  exact Universal.rule_168 (a k) (relation_zero k)
lemma rule_169 : word (a k) [9, 41, 44, 59]=0 := by
  exact Universal.rule_169 (a k) (relation_zero k)
lemma rule_170 : word (a k) [35, 56, 43, 48] + (-word (a k) [35, 55, 27, 59])=0 := by
  exact Universal.rule_170 (a k) (relation_zero k)
lemma rule_171 : (-word (a k) [52, 41, 43, 48]) + word (a k) [52, 41, 44, 59]=0 := by
  exact Universal.rule_171 (a k) (relation_zero k)
lemma rule_172 : word (a k) [52, 42, 45, 6] + (-word (a k) [52, 41, 43, 47])=0 := by
  exact Universal.rule_172 (a k) (relation_zero k)
lemma rule_173 : (-word (a k) [41, 43, 47, 7]) + word (a k) [41, 43, 48, 50]=0 := by
  exact Universal.rule_173 (a k) (relation_zero k)
lemma rule_174 : word (a k) [56, 43, 47, 7] + (-word (a k) [55, 27, 59, 50])=0 := by
  exact Universal.rule_174 (a k) (relation_zero k)
lemma rule_175 : word (a k) [33, 13, 49, 70]=0 := by
  exact Universal.rule_175 (a k) (relation_zero k)
lemma rule_176 : (-word (a k) [50, 17, 21, 70]) + word (a k) [51, 64, 36, 70]=0 := by
  exact Universal.rule_176 (a k) (relation_zero k)
lemma rule_177 : word (a k) [27, 59, 50, 17] + (-word (a k) [27, 58, 34, 63])=0 := by
  exact Universal.rule_177 (a k) (relation_zero k)
lemma rule_178 : (-word (a k) [43, 47, 7, 17]) + word (a k) [43, 48, 51, 63]=0 := by
  exact Universal.rule_178 (a k) (relation_zero k)
lemma rule_179 : (-word (a k) [45, 6, 7, 17]) + word (a k) [46, 48, 51, 63]=0 := by
  exact Universal.rule_179 (a k) (relation_zero k)
lemma rule_180 : (-word (a k) [24, 18, 9, 41]) + word (a k) [24, 19, 53, 56]=0 := by
  exact Universal.rule_180 (a k) (relation_zero k)
lemma rule_181 : (-word (a k) [28, 14, 9, 41]) + word (a k) [29, 19, 53, 56]=0 := by
  exact Universal.rule_181 (a k) (relation_zero k)
lemma rule_182 : word (a k) [32, 62, 52, 41] + (-word (a k) [32, 61, 35, 56])=0 := by
  exact Universal.rule_182 (a k) (relation_zero k)
lemma rule_183 : word (a k) [40, 62, 52, 41] + (-word (a k) [40, 60, 4, 56]) + (-word (a k) [39, 12, 35, 56])=0 := by
  exact Universal.rule_183 (a k) (relation_zero k)
lemma rule_184 : (-word (a k) [12, 35, 55, 27]) + word (a k) [12, 35, 56, 44]=0 := by
  exact Universal.rule_184 (a k) (relation_zero k)
lemma rule_185 : word (a k) [19, 53, 54, 16] + (-word (a k) [18, 9, 41, 44])=0 := by
  exact Universal.rule_185 (a k) (relation_zero k)
lemma rule_186 : (-word (a k) [60, 4, 54, 16]) + word (a k) [60, 4, 56, 44]=0 := by
  exact Universal.rule_186 (a k) (relation_zero k)
lemma rule_187 : (-word (a k) [61, 35, 55, 27]) + word (a k) [61, 35, 56, 44]=0 := by
  exact Universal.rule_187 (a k) (relation_zero k)
lemma rule_188 : (-word (a k) [41, 44, 57, 5]) + word (a k) [41, 44, 58, 34] + (-word (a k) [41, 43, 48, 51])=0 := by
  exact Universal.rule_188 (a k) (relation_zero k)
lemma rule_189 : word (a k) [54, 16, 57, 5] + (-word (a k) [54, 15, 1, 34])=0 := by
  exact Universal.rule_189 (a k) (relation_zero k)
lemma rule_190 : (-word (a k) [55, 27, 58, 34]) + word (a k) [55, 27, 59, 51]=0 := by
  exact Universal.rule_190 (a k) (relation_zero k)
lemma rule_191 : (-word (a k) [3, 40, 60, 4]) + word (a k) [3, 40, 62, 53]=0 := by
  exact Universal.rule_191 (a k) (relation_zero k)
lemma rule_192 : word (a k) [37, 25, 60, 4] + (-word (a k) [37, 24, 19, 53])=0 := by
  exact Universal.rule_192 (a k) (relation_zero k)
lemma rule_193 : word (a k) [66, 25, 60, 4] + (-word (a k) [66, 24, 19, 53])=0 := by
  exact Universal.rule_193 (a k) (relation_zero k)
lemma rule_194 : (-word (a k) [67, 32, 61, 35]) + word (a k) [67, 32, 62, 53]=0 := by
  exact Universal.rule_194 (a k) (relation_zero k)
lemma rule_195 : word (a k) [1, 34, 63, 21]=0 := by
  exact Universal.rule_195 (a k) (relation_zero k)
lemma rule_196 : word (a k) [47, 7, 17, 21] + (-word (a k) [48, 51, 64, 36]) + word (a k) [48, 51, 65, 49]=0 := by
  exact Universal.rule_196 (a k) (relation_zero k)
lemma rule_197 : word (a k) [57, 5, 63, 21]=0 := by
  exact Universal.rule_197 (a k) (relation_zero k)
lemma rule_198 : (-word (a k) [58, 34, 63, 21]) + word (a k) [58, 34, 64, 36] + (-word (a k) [58, 33, 13, 49])=0 := by
  exact Universal.rule_198 (a k) (relation_zero k)
lemma rule_199 : (-word (a k) [31, 73, 67, 32]) + word (a k) [31, 73, 68, 40]=0 := by
  exact Universal.rule_199 (a k) (relation_zero k)
lemma rule_200 : word (a k) [69, 8, 66, 25] + word (a k) [69, 8, 68, 40]=0 := by
  exact Universal.rule_200 (a k) (relation_zero k)
lemma rule_201 : word (a k) [70, 23, 66, 25] + (-word (a k) [70, 22, 3, 40])=0 := by
  exact Universal.rule_201 (a k) (relation_zero k)
lemma rule_202 : (-word (a k) [13, 49, 69, 8]) + word (a k) [13, 49, 71, 73]=0 := by
  exact Universal.rule_202 (a k) (relation_zero k)
lemma rule_203 : word (a k) [17, 21, 69, 8] + word (a k) [17, 21, 70, 23]=0 := by
  exact Universal.rule_203 (a k) (relation_zero k)
lemma rule_204 : word (a k) [63, 21, 69, 8] + word (a k) [63, 21, 70, 23]=0 := by
  exact Universal.rule_204 (a k) (relation_zero k)
lemma rule_205 : word (a k) [64, 36, 71, 73] + word (a k) [63, 21, 69, 8]=0 := by
  exact Universal.rule_205 (a k) (relation_zero k)
lemma rule_206 : word (a k) [26, 31, 73, 66]=0 := by
  exact Universal.rule_206 (a k) (relation_zero k)
lemma rule_207 : word (a k) [36, 71, 72, 37] + (-word (a k) [36, 70, 23, 66])=0 := by
  exact Universal.rule_207 (a k) (relation_zero k)
lemma rule_208 : word (a k) [49, 71, 72, 37] + (-word (a k) [49, 69, 8, 66])=0 := by
  exact Universal.rule_208 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
