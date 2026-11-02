import N6UniversalDefining
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_0 : word v [1, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_0 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_1 : word v [3, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_2 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_2 : word v [4, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_4 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_3 : word v [5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_6 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_4 : word v [5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_5 : word v [8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_6 : word v [9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_11 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_7 : (-word v [15, 1]) + word v [16, 58]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_12 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_8 : word v [16, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_13 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_9 : word v [17, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_14 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_10 : (-word v [18, 9]) + word v [19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_11 : word v [20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_12 : word v [21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_13 : word v [23, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_19 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_14 : word v [22, 3] + word v [23, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_20 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_15 : word v [25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_16 : (-word v [24, 19]) + word v [25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_17 : word v [26, 30]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_23 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_18 : word v [27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_19 : (-word v [28, 14]) + word v [29, 18]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_25 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_20 : word v [31, 72]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_26 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_21 : word v [32, 60]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_27 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_22 : (-word v [33, 13]) + word v [34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_23 : word v [35, 54]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_29 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_24 : word v [36, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_30 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_25 : (-word v [37, 24]) + word v [38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_31 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_26 : (-word v [39, 12]) + word v [40, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_32 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_27 : (-word v [41, 43]) + word v [42, 46]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_33 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_28 : (-word v [43, 48]) + word v [44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_34 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_29 : (-word v [45, 6]) + word v [46, 47]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_35 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_30 : (-word v [47, 7]) + word v [48, 50]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_36 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_31 : word v [49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_32 : (-word v [50, 17]) + word v [51, 63]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_38 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_33 : (-word v [52, 41]) + word v [53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_39 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_34 : (-word v [54, 16]) + (-word v [55, 27]) + word v [56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_40 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_35 : word v [57, 5] + (-word v [58, 34]) + word v [59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_41 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_36 : (-word v [60, 4]) + (-word v [61, 35]) + word v [62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_42 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_37 : word v [63, 21] + (-word v [64, 36]) + word v [65, 49]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_43 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_38 : word v [66, 25] + (-word v [67, 32]) + word v [68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_44 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_39 : (-word v [69, 8]) + (-word v [70, 23]) + word v [71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_45 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_40 : (-word v [72, 37]) + word v [73, 66]=0 := by
  have h0 := congrArg (fun x : A => x * word v []) (defining_46 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_0 : word (a k) [1, 33]=0 := by
  exact Universal.rule_0 (a k) (relation_zero k)
lemma rule_1 : word (a k) [3, 39]=0 := by
  exact Universal.rule_1 (a k) (relation_zero k)
lemma rule_2 : word (a k) [4, 55]=0 := by
  exact Universal.rule_2 (a k) (relation_zero k)
lemma rule_3 : word (a k) [5, 64]=0 := by
  exact Universal.rule_3 (a k) (relation_zero k)
lemma rule_4 : word (a k) [5, 65]=0 := by
  exact Universal.rule_4 (a k) (relation_zero k)
lemma rule_5 : word (a k) [8, 67]=0 := by
  exact Universal.rule_5 (a k) (relation_zero k)
lemma rule_6 : word (a k) [9, 42]=0 := by
  exact Universal.rule_6 (a k) (relation_zero k)
lemma rule_7 : (-word (a k) [15, 1]) + word (a k) [16, 58]=0 := by
  exact Universal.rule_7 (a k) (relation_zero k)
lemma rule_8 : word (a k) [16, 59]=0 := by
  exact Universal.rule_8 (a k) (relation_zero k)
lemma rule_9 : word (a k) [17, 20]=0 := by
  exact Universal.rule_9 (a k) (relation_zero k)
lemma rule_10 : (-word (a k) [18, 9]) + word (a k) [19, 52]=0 := by
  exact Universal.rule_10 (a k) (relation_zero k)
lemma rule_11 : word (a k) [20, 31]=0 := by
  exact Universal.rule_11 (a k) (relation_zero k)
lemma rule_12 : word (a k) [21, 71]=0 := by
  exact Universal.rule_12 (a k) (relation_zero k)
lemma rule_13 : word (a k) [23, 67]=0 := by
  exact Universal.rule_13 (a k) (relation_zero k)
lemma rule_14 : word (a k) [22, 3] + word (a k) [23, 68]=0 := by
  exact Universal.rule_14 (a k) (relation_zero k)
lemma rule_15 : word (a k) [25, 61]=0 := by
  exact Universal.rule_15 (a k) (relation_zero k)
lemma rule_16 : (-word (a k) [24, 19]) + word (a k) [25, 62]=0 := by
  exact Universal.rule_16 (a k) (relation_zero k)
lemma rule_17 : word (a k) [26, 30]=0 := by
  exact Universal.rule_17 (a k) (relation_zero k)
lemma rule_18 : word (a k) [27, 57]=0 := by
  exact Universal.rule_18 (a k) (relation_zero k)
lemma rule_19 : (-word (a k) [28, 14]) + word (a k) [29, 18]=0 := by
  exact Universal.rule_19 (a k) (relation_zero k)
lemma rule_20 : word (a k) [31, 72]=0 := by
  exact Universal.rule_20 (a k) (relation_zero k)
lemma rule_21 : word (a k) [32, 60]=0 := by
  exact Universal.rule_21 (a k) (relation_zero k)
lemma rule_22 : (-word (a k) [33, 13]) + word (a k) [34, 65]=0 := by
  exact Universal.rule_22 (a k) (relation_zero k)
lemma rule_23 : word (a k) [35, 54]=0 := by
  exact Universal.rule_23 (a k) (relation_zero k)
lemma rule_24 : word (a k) [36, 69]=0 := by
  exact Universal.rule_24 (a k) (relation_zero k)
lemma rule_25 : (-word (a k) [37, 24]) + word (a k) [38, 29]=0 := by
  exact Universal.rule_25 (a k) (relation_zero k)
lemma rule_26 : (-word (a k) [39, 12]) + word (a k) [40, 61]=0 := by
  exact Universal.rule_26 (a k) (relation_zero k)
lemma rule_27 : (-word (a k) [41, 43]) + word (a k) [42, 46]=0 := by
  exact Universal.rule_27 (a k) (relation_zero k)
lemma rule_28 : (-word (a k) [43, 48]) + word (a k) [44, 59]=0 := by
  exact Universal.rule_28 (a k) (relation_zero k)
lemma rule_29 : (-word (a k) [45, 6]) + word (a k) [46, 47]=0 := by
  exact Universal.rule_29 (a k) (relation_zero k)
lemma rule_30 : (-word (a k) [47, 7]) + word (a k) [48, 50]=0 := by
  exact Universal.rule_30 (a k) (relation_zero k)
lemma rule_31 : word (a k) [49, 70]=0 := by
  exact Universal.rule_31 (a k) (relation_zero k)
lemma rule_32 : (-word (a k) [50, 17]) + word (a k) [51, 63]=0 := by
  exact Universal.rule_32 (a k) (relation_zero k)
lemma rule_33 : (-word (a k) [52, 41]) + word (a k) [53, 56]=0 := by
  exact Universal.rule_33 (a k) (relation_zero k)
lemma rule_34 : (-word (a k) [54, 16]) + (-word (a k) [55, 27]) + word (a k) [56, 44]=0 := by
  exact Universal.rule_34 (a k) (relation_zero k)
lemma rule_35 : word (a k) [57, 5] + (-word (a k) [58, 34]) + word (a k) [59, 51]=0 := by
  exact Universal.rule_35 (a k) (relation_zero k)
lemma rule_36 : (-word (a k) [60, 4]) + (-word (a k) [61, 35]) + word (a k) [62, 53]=0 := by
  exact Universal.rule_36 (a k) (relation_zero k)
lemma rule_37 : word (a k) [63, 21] + (-word (a k) [64, 36]) + word (a k) [65, 49]=0 := by
  exact Universal.rule_37 (a k) (relation_zero k)
lemma rule_38 : word (a k) [66, 25] + (-word (a k) [67, 32]) + word (a k) [68, 40]=0 := by
  exact Universal.rule_38 (a k) (relation_zero k)
lemma rule_39 : (-word (a k) [69, 8]) + (-word (a k) [70, 23]) + word (a k) [71, 73]=0 := by
  exact Universal.rule_39 (a k) (relation_zero k)
lemma rule_40 : (-word (a k) [72, 37]) + word (a k) [73, 66]=0 := by
  exact Universal.rule_40 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
