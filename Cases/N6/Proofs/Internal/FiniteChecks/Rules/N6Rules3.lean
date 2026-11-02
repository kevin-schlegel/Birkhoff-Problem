import N6Rules2
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_41 : word v [15, 1, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [15]) (defining_0 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_42 : word v [1, 34, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_1 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_43 : word v [22, 3, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [22]) (defining_2 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_44 : word v [60, 4, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [60]) (defining_4 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_45 : word v [4, 56, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_5 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_46 : word v [57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [57]) (defining_6 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_47 : word v [57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_48 : word v [8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_8 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_49 : word v [69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_50 : word v [14, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [14]) (defining_11 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_51 : word v [18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [18]) (defining_11 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_52 : (-word v [54, 15, 1]) + word v [54, 16, 58]=0 := by
  have h0 := congrArg (fun x : A => x * word v [54]) (defining_12 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_53 : word v [54, 16, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [54]) (defining_13 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_54 : word v [7, 17, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7]) (defining_14 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_55 : word v [50, 17, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50]) (defining_14 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_56 : word v [19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_15 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_57 : (-word v [24, 18, 9]) + word v [24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_58 : (-word v [28, 14, 9]) + word v [29, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [29]) (defining_16 v H)
  have h1 := congrArg (fun x : A => word v [9] * x) (rule_19 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_59 : word v [63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_60 : word v [17, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_61 : word v [63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_62 : word v [70, 23, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70]) (defining_19 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_63 : word v [70, 22, 3] + word v [70, 23, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70]) (defining_20 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_64 : word v [37, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_65 : word v [66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_66 : (-word v [37, 24, 19]) + word v [37, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_67 : (-word v [66, 24, 19]) + word v [66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_68 : word v [11, 26, 30]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11]) (defining_23 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_69 : word v [55, 27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55]) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_70 : word v [38, 28, 14] + (-word v [37, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_25 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_71 : word v [26, 31, 72]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26]) (defining_26 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_72 : word v [67, 32, 60]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67]) (defining_27 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_73 : word v [1, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [1]) (defining_28 v H)
  have h1 := congrArg (fun x : A => word v [13] * x) (rule_0 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_74 : (-word v [58, 33, 13]) + word v [58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_75 : word v [12, 35, 54]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12]) (defining_29 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_76 : word v [61, 35, 54]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61]) (defining_29 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_77 : word v [64, 36, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [64]) (defining_30 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_78 : (-word v [72, 37, 24]) + word v [72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72]) (defining_31 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_79 : word v [3, 40, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [3]) (defining_32 v H)
  have h1 := congrArg (fun x : A => word v [12] * x) (rule_1 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_80 : word v [68, 39, 12] + (-word v [67, 32, 61])=0 := by
  have h0 := congrArg (fun x : A => x * word v [68]) (defining_32 v H)
  have h1 := congrArg (fun x : A => word v [61] * x) (rule_38 v H)
  have h2 := congrArg (fun x : A => word v [] * x) (rule_65 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (-1) * h2
lemma rule_81 : word v [9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [9]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [46] * x) (rule_6 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_82 : (-word v [52, 41, 43]) + word v [52, 42, 46]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52]) (defining_33 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_83 : (-word v [41, 43, 48]) + word v [41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41]) (defining_34 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_84 : word v [56, 43, 48] + (-word v [55, 27, 59])=0 := by
  have h0 := congrArg (fun x : A => x * word v [56]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_34 v H)
  have h2 := congrArg (fun x : A => word v [] * x) (rule_53 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2
lemma rule_85 : word v [42, 45, 6] + (-word v [41, 43, 47])=0 := by
  have h0 := congrArg (fun x : A => x * word v [42]) (defining_35 v H)
  have h1 := congrArg (fun x : A => word v [47] * x) (rule_27 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_86 : (-word v [43, 47, 7]) + word v [43, 48, 50]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43]) (defining_36 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_87 : (-word v [45, 6, 7]) + word v [46, 48, 50]=0 := by
  have h0 := congrArg (fun x : A => x * word v [46]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [7] * x) (rule_29 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_88 : word v [13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_89 : (-word v [63, 21, 70]) + word v [64, 36, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [65]) (defining_37 v H)
  have h1 := congrArg (fun x : A => word v [70] * x) (rule_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_90 : (-word v [47, 7, 17]) + word v [48, 51, 63]=0 := by
  have h0 := congrArg (fun x : A => x * word v [48]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [17] * x) (rule_30 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_91 : word v [59, 50, 17] + word v [57, 5, 63] + (-word v [58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_35 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_92 : (-word v [18, 9, 41]) + word v [19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_10 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_93 : word v [62, 52, 41] + (-word v [60, 4, 56]) + (-word v [61, 35, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_36 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_94 : (-word v [4, 54, 16]) + word v [4, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [4]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_2 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_95 : (-word v [35, 55, 27]) + word v [35, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [16] * x) (rule_23 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_96 : word v [53, 54, 16] + word v [53, 55, 27] + (-word v [52, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [44] * x) (rule_33 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_97 : word v [16, 57, 5] + (-word v [15, 1, 34])=0 := by
  have h0 := congrArg (fun x : A => x * word v [16]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [34] * x) (rule_7 v H)
  have h2 := congrArg (fun x : A => word v [51] * x) (rule_8 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_98 : (-word v [27, 58, 34]) + word v [27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_99 : (-word v [44, 57, 5]) + word v [44, 58, 34] + (-word v [43, 48, 51])=0 := by
  have h0 := congrArg (fun x : A => x * word v [44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_100 : word v [25, 60, 4] + (-word v [24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_15 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_101 : (-word v [32, 61, 35]) + word v [32, 62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [4] * x) (rule_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_102 : (-word v [40, 60, 4]) + (-word v [39, 12, 35]) + word v [40, 62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v [40]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_26 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_103 : word v [5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_3 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_4 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_104 : (-word v [34, 63, 21]) + word v [34, 64, 36] + (-word v [33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_105 : word v [50, 17, 21] + (-word v [51, 64, 36]) + word v [51, 65, 49]=0 := by
  have h0 := congrArg (fun x : A => x * word v [51]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [21] * x) (rule_32 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_106 : word v [8, 66, 25] + word v [8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_5 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_107 : word v [23, 66, 25] + (-word v [22, 3, 40])=0 := by
  have h0 := congrArg (fun x : A => x * word v [23]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_13 v H)
  have h2 := congrArg (fun x : A => word v [40] * x) (rule_14 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_108 : word v [72, 37, 25] + (-word v [73, 67, 32]) + word v [73, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [25] * x) (rule_40 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_109 : word v [21, 69, 8] + word v [21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [73] * x) (rule_12 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_110 : (-word v [36, 70, 23]) + word v [36, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_111 : (-word v [49, 69, 8]) + word v [49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_31 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_112 : word v [31, 73, 66]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [37] * x) (rule_20 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_113 : word v [71, 72, 37] + (-word v [69, 8, 66]) + (-word v [70, 23, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_39 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_41 : word (a k) [15, 1, 33]=0 := by
  exact Universal.rule_41 (a k) (relation_zero k)
lemma rule_42 : word (a k) [1, 34, 64]=0 := by
  exact Universal.rule_42 (a k) (relation_zero k)
lemma rule_43 : word (a k) [22, 3, 39]=0 := by
  exact Universal.rule_43 (a k) (relation_zero k)
lemma rule_44 : word (a k) [60, 4, 55]=0 := by
  exact Universal.rule_44 (a k) (relation_zero k)
lemma rule_45 : word (a k) [4, 56, 43]=0 := by
  exact Universal.rule_45 (a k) (relation_zero k)
lemma rule_46 : word (a k) [57, 5, 64]=0 := by
  exact Universal.rule_46 (a k) (relation_zero k)
lemma rule_47 : word (a k) [57, 5, 65]=0 := by
  exact Universal.rule_47 (a k) (relation_zero k)
lemma rule_48 : word (a k) [8, 68, 39]=0 := by
  exact Universal.rule_48 (a k) (relation_zero k)
lemma rule_49 : word (a k) [69, 8, 67]=0 := by
  exact Universal.rule_49 (a k) (relation_zero k)
lemma rule_50 : word (a k) [14, 9, 42]=0 := by
  exact Universal.rule_50 (a k) (relation_zero k)
lemma rule_51 : word (a k) [18, 9, 42]=0 := by
  exact Universal.rule_51 (a k) (relation_zero k)
lemma rule_52 : (-word (a k) [54, 15, 1]) + word (a k) [54, 16, 58]=0 := by
  exact Universal.rule_52 (a k) (relation_zero k)
lemma rule_53 : word (a k) [54, 16, 59]=0 := by
  exact Universal.rule_53 (a k) (relation_zero k)
lemma rule_54 : word (a k) [7, 17, 20]=0 := by
  exact Universal.rule_54 (a k) (relation_zero k)
lemma rule_55 : word (a k) [50, 17, 20]=0 := by
  exact Universal.rule_55 (a k) (relation_zero k)
lemma rule_56 : word (a k) [19, 53, 55]=0 := by
  exact Universal.rule_56 (a k) (relation_zero k)
lemma rule_57 : (-word (a k) [24, 18, 9]) + word (a k) [24, 19, 52]=0 := by
  exact Universal.rule_57 (a k) (relation_zero k)
lemma rule_58 : (-word (a k) [28, 14, 9]) + word (a k) [29, 19, 52]=0 := by
  exact Universal.rule_58 (a k) (relation_zero k)
lemma rule_59 : word (a k) [63, 20, 31]=0 := by
  exact Universal.rule_59 (a k) (relation_zero k)
lemma rule_60 : word (a k) [17, 21, 71]=0 := by
  exact Universal.rule_60 (a k) (relation_zero k)
lemma rule_61 : word (a k) [63, 21, 71]=0 := by
  exact Universal.rule_61 (a k) (relation_zero k)
lemma rule_62 : word (a k) [70, 23, 67]=0 := by
  exact Universal.rule_62 (a k) (relation_zero k)
lemma rule_63 : word (a k) [70, 22, 3] + word (a k) [70, 23, 68]=0 := by
  exact Universal.rule_63 (a k) (relation_zero k)
lemma rule_64 : word (a k) [37, 25, 61]=0 := by
  exact Universal.rule_64 (a k) (relation_zero k)
lemma rule_65 : word (a k) [66, 25, 61]=0 := by
  exact Universal.rule_65 (a k) (relation_zero k)
lemma rule_66 : (-word (a k) [37, 24, 19]) + word (a k) [37, 25, 62]=0 := by
  exact Universal.rule_66 (a k) (relation_zero k)
lemma rule_67 : (-word (a k) [66, 24, 19]) + word (a k) [66, 25, 62]=0 := by
  exact Universal.rule_67 (a k) (relation_zero k)
lemma rule_68 : word (a k) [11, 26, 30]=0 := by
  exact Universal.rule_68 (a k) (relation_zero k)
lemma rule_69 : word (a k) [55, 27, 57]=0 := by
  exact Universal.rule_69 (a k) (relation_zero k)
lemma rule_70 : word (a k) [38, 28, 14] + (-word (a k) [37, 24, 18])=0 := by
  exact Universal.rule_70 (a k) (relation_zero k)
lemma rule_71 : word (a k) [26, 31, 72]=0 := by
  exact Universal.rule_71 (a k) (relation_zero k)
lemma rule_72 : word (a k) [67, 32, 60]=0 := by
  exact Universal.rule_72 (a k) (relation_zero k)
lemma rule_73 : word (a k) [1, 34, 65]=0 := by
  exact Universal.rule_73 (a k) (relation_zero k)
lemma rule_74 : (-word (a k) [58, 33, 13]) + word (a k) [58, 34, 65]=0 := by
  exact Universal.rule_74 (a k) (relation_zero k)
lemma rule_75 : word (a k) [12, 35, 54]=0 := by
  exact Universal.rule_75 (a k) (relation_zero k)
lemma rule_76 : word (a k) [61, 35, 54]=0 := by
  exact Universal.rule_76 (a k) (relation_zero k)
lemma rule_77 : word (a k) [64, 36, 69]=0 := by
  exact Universal.rule_77 (a k) (relation_zero k)
lemma rule_78 : (-word (a k) [72, 37, 24]) + word (a k) [72, 38, 29]=0 := by
  exact Universal.rule_78 (a k) (relation_zero k)
lemma rule_79 : word (a k) [3, 40, 61]=0 := by
  exact Universal.rule_79 (a k) (relation_zero k)
lemma rule_80 : word (a k) [68, 39, 12] + (-word (a k) [67, 32, 61])=0 := by
  exact Universal.rule_80 (a k) (relation_zero k)
lemma rule_81 : word (a k) [9, 41, 43]=0 := by
  exact Universal.rule_81 (a k) (relation_zero k)
lemma rule_82 : (-word (a k) [52, 41, 43]) + word (a k) [52, 42, 46]=0 := by
  exact Universal.rule_82 (a k) (relation_zero k)
lemma rule_83 : (-word (a k) [41, 43, 48]) + word (a k) [41, 44, 59]=0 := by
  exact Universal.rule_83 (a k) (relation_zero k)
lemma rule_84 : word (a k) [56, 43, 48] + (-word (a k) [55, 27, 59])=0 := by
  exact Universal.rule_84 (a k) (relation_zero k)
lemma rule_85 : word (a k) [42, 45, 6] + (-word (a k) [41, 43, 47])=0 := by
  exact Universal.rule_85 (a k) (relation_zero k)
lemma rule_86 : (-word (a k) [43, 47, 7]) + word (a k) [43, 48, 50]=0 := by
  exact Universal.rule_86 (a k) (relation_zero k)
lemma rule_87 : (-word (a k) [45, 6, 7]) + word (a k) [46, 48, 50]=0 := by
  exact Universal.rule_87 (a k) (relation_zero k)
lemma rule_88 : word (a k) [13, 49, 70]=0 := by
  exact Universal.rule_88 (a k) (relation_zero k)
lemma rule_89 : (-word (a k) [63, 21, 70]) + word (a k) [64, 36, 70]=0 := by
  exact Universal.rule_89 (a k) (relation_zero k)
lemma rule_90 : (-word (a k) [47, 7, 17]) + word (a k) [48, 51, 63]=0 := by
  exact Universal.rule_90 (a k) (relation_zero k)
lemma rule_91 : word (a k) [59, 50, 17] + word (a k) [57, 5, 63] + (-word (a k) [58, 34, 63])=0 := by
  exact Universal.rule_91 (a k) (relation_zero k)
lemma rule_92 : (-word (a k) [18, 9, 41]) + word (a k) [19, 53, 56]=0 := by
  exact Universal.rule_92 (a k) (relation_zero k)
lemma rule_93 : word (a k) [62, 52, 41] + (-word (a k) [60, 4, 56]) + (-word (a k) [61, 35, 56])=0 := by
  exact Universal.rule_93 (a k) (relation_zero k)
lemma rule_94 : (-word (a k) [4, 54, 16]) + word (a k) [4, 56, 44]=0 := by
  exact Universal.rule_94 (a k) (relation_zero k)
lemma rule_95 : (-word (a k) [35, 55, 27]) + word (a k) [35, 56, 44]=0 := by
  exact Universal.rule_95 (a k) (relation_zero k)
lemma rule_96 : word (a k) [53, 54, 16] + word (a k) [53, 55, 27] + (-word (a k) [52, 41, 44])=0 := by
  exact Universal.rule_96 (a k) (relation_zero k)
lemma rule_97 : word (a k) [16, 57, 5] + (-word (a k) [15, 1, 34])=0 := by
  exact Universal.rule_97 (a k) (relation_zero k)
lemma rule_98 : (-word (a k) [27, 58, 34]) + word (a k) [27, 59, 51]=0 := by
  exact Universal.rule_98 (a k) (relation_zero k)
lemma rule_99 : (-word (a k) [44, 57, 5]) + word (a k) [44, 58, 34] + (-word (a k) [43, 48, 51])=0 := by
  exact Universal.rule_99 (a k) (relation_zero k)
lemma rule_100 : word (a k) [25, 60, 4] + (-word (a k) [24, 19, 53])=0 := by
  exact Universal.rule_100 (a k) (relation_zero k)
lemma rule_101 : (-word (a k) [32, 61, 35]) + word (a k) [32, 62, 53]=0 := by
  exact Universal.rule_101 (a k) (relation_zero k)
lemma rule_102 : (-word (a k) [40, 60, 4]) + (-word (a k) [39, 12, 35]) + word (a k) [40, 62, 53]=0 := by
  exact Universal.rule_102 (a k) (relation_zero k)
lemma rule_103 : word (a k) [5, 63, 21]=0 := by
  exact Universal.rule_103 (a k) (relation_zero k)
lemma rule_104 : (-word (a k) [34, 63, 21]) + word (a k) [34, 64, 36] + (-word (a k) [33, 13, 49])=0 := by
  exact Universal.rule_104 (a k) (relation_zero k)
lemma rule_105 : word (a k) [50, 17, 21] + (-word (a k) [51, 64, 36]) + word (a k) [51, 65, 49]=0 := by
  exact Universal.rule_105 (a k) (relation_zero k)
lemma rule_106 : word (a k) [8, 66, 25] + word (a k) [8, 68, 40]=0 := by
  exact Universal.rule_106 (a k) (relation_zero k)
lemma rule_107 : word (a k) [23, 66, 25] + (-word (a k) [22, 3, 40])=0 := by
  exact Universal.rule_107 (a k) (relation_zero k)
lemma rule_108 : word (a k) [72, 37, 25] + (-word (a k) [73, 67, 32]) + word (a k) [73, 68, 40]=0 := by
  exact Universal.rule_108 (a k) (relation_zero k)
lemma rule_109 : word (a k) [21, 69, 8] + word (a k) [21, 70, 23]=0 := by
  exact Universal.rule_109 (a k) (relation_zero k)
lemma rule_110 : (-word (a k) [36, 70, 23]) + word (a k) [36, 71, 73]=0 := by
  exact Universal.rule_110 (a k) (relation_zero k)
lemma rule_111 : (-word (a k) [49, 69, 8]) + word (a k) [49, 71, 73]=0 := by
  exact Universal.rule_111 (a k) (relation_zero k)
lemma rule_112 : word (a k) [31, 73, 66]=0 := by
  exact Universal.rule_112 (a k) (relation_zero k)
lemma rule_113 : word (a k) [71, 72, 37] + (-word (a k) [69, 8, 66]) + (-word (a k) [70, 23, 66])=0 := by
  exact Universal.rule_113 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
