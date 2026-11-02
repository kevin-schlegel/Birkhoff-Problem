import N6NormalData
import N6Reduced0
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_50_39 : a k 39*normalRep k 50=0 := by
  change a k 39*walk k 3 [3]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1 (a k) (relation_zero k) (e k 3)
lemma extension_50_40 : a k 40*normalRep k 50=normalRep k 124 := by
  exact (walk_snoc k 3 [3] 40).symm
lemma arrow_span_50 (b : Fin 75) : a k b*normalRep k 50 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_50_39 k]
      exact Submodule.zero_mem _
    · rw [extension_50_40 k]
      exact normal_mem k 124
  · rw [show a k b*normalRep k 50=0 from arrow_incompatible k b 3 30 [3] (normal_endpoints 50) h]
    exact Submodule.zero_mem _
lemma extension_51_54 : a k 54*normalRep k 51=normalRep k 125 := by
  exact (walk_snoc k 4 [4] 54).symm
lemma extension_51_55 : a k 55*normalRep k 51=0 := by
  change a k 55*walk k 4 [4]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_2 (a k) (relation_zero k) (e k 4)
lemma extension_51_56 : a k 56*normalRep k 51=normalRep k 126 := by
  exact (walk_snoc k 4 [4] 56).symm
lemma arrow_span_51 (b : Fin 75) : a k b*normalRep k 51 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_51_54 k]
      exact normal_mem k 125
    · rw [extension_51_55 k]
      exact Submodule.zero_mem _
    · rw [extension_51_56 k]
      exact normal_mem k 126
  · rw [show a k b*normalRep k 51=0 from arrow_incompatible k b 4 38 [4] (normal_endpoints 51) h]
    exact Submodule.zero_mem _
lemma extension_52_63 : a k 63*normalRep k 52=normalRep k 127 := by
  exact (walk_snoc k 5 [5] 63).symm
lemma extension_52_64 : a k 64*normalRep k 52=0 := by
  change a k 64*walk k 5 [5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_3 (a k) (relation_zero k) (e k 5)
lemma extension_52_65 : a k 65*normalRep k 52=0 := by
  change a k 65*walk k 5 [5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_4 (a k) (relation_zero k) (e k 5)
lemma arrow_span_52 (b : Fin 75) : a k b*normalRep k 52 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_52_63 k]
      exact normal_mem k 127
    · rw [extension_52_64 k]
      exact Submodule.zero_mem _
    · rw [extension_52_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 52=0 from arrow_incompatible k b 5 41 [5] (normal_endpoints 52) h]
    exact Submodule.zero_mem _
lemma extension_53_7 : a k 7*normalRep k 53=normalRep k 128 := by
  exact (walk_snoc k 6 [6] 7).symm
lemma arrow_span_53 (b : Fin 75) : a k b*normalRep k 53 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_53_7 k]
      exact normal_mem k 128
  · rw [show a k b*normalRep k 53=0 from arrow_incompatible k b 6 7 [6] (normal_endpoints 53) h]
    exact Submodule.zero_mem _
lemma extension_54_17 : a k 17*normalRep k 54=normalRep k 129 := by
  exact (walk_snoc k 7 [7] 17).symm
lemma arrow_span_54 (b : Fin 75) : a k b*normalRep k 54 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_54_17 k]
      exact normal_mem k 129
  · rw [show a k b*normalRep k 54=0 from arrow_incompatible k b 7 16 [7] (normal_endpoints 54) h]
    exact Submodule.zero_mem _
lemma extension_55_66 : a k 66*normalRep k 55=normalRep k 130 := by
  exact (walk_snoc k 8 [8] 66).symm
lemma extension_55_67 : a k 67*normalRep k 55=0 := by
  change a k 67*walk k 8 [8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_5 (a k) (relation_zero k) (e k 8)
lemma extension_55_68 : a k 68*normalRep k 55=normalRep k 131 := by
  exact (walk_snoc k 8 [8] 68).symm
lemma arrow_span_55 (b : Fin 75) : a k b*normalRep k 55 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_55_66 k]
      exact normal_mem k 130
    · rw [extension_55_67 k]
      exact Submodule.zero_mem _
    · rw [extension_55_68 k]
      exact normal_mem k 131
  · rw [show a k b*normalRep k 55=0 from arrow_incompatible k b 8 42 [8] (normal_endpoints 55) h]
    exact Submodule.zero_mem _
lemma extension_56_41 : a k 41*normalRep k 56=normalRep k 132 := by
  exact (walk_snoc k 9 [9] 41).symm
lemma extension_56_42 : a k 42*normalRep k 56=0 := by
  change a k 42*walk k 9 [9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_6 (a k) (relation_zero k) (e k 9)
lemma arrow_span_56 (b : Fin 75) : a k b*normalRep k 56 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_56_41 k]
      exact normal_mem k 132
    · rw [extension_56_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 56=0 from arrow_incompatible k b 9 31 [9] (normal_endpoints 56) h]
    exact Submodule.zero_mem _
lemma extension_57_11 : a k 11*normalRep k 57=normalRep k 133 := by
  exact (walk_snoc k 10 [10] 11).symm
lemma arrow_span_57 (b : Fin 75) : a k b*normalRep k 57 ∈ normalSpan k := by
  by_cases h : arrowSource b=11
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [11] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_57_11 k]
      exact normal_mem k 133
  · rw [show a k b*normalRep k 57=0 from arrow_incompatible k b 10 11 [10] (normal_endpoints 57) h]
    exact Submodule.zero_mem _
lemma extension_58_26 : a k 26*normalRep k 58=normalRep k 134 := by
  exact (walk_snoc k 11 [11] 26).symm
lemma arrow_span_58 (b : Fin 75) : a k b*normalRep k 58 ∈ normalSpan k := by
  by_cases h : arrowSource b=21
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [26] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_58_26 k]
      exact normal_mem k 134
  · rw [show a k b*normalRep k 58=0 from arrow_incompatible k b 11 21 [11] (normal_endpoints 58) h]
    exact Submodule.zero_mem _
lemma extension_59_35 : a k 35*normalRep k 59=normalRep k 135 := by
  exact (walk_snoc k 12 [12] 35).symm
lemma arrow_span_59 (b : Fin 75) : a k b*normalRep k 59 ∈ normalSpan k := by
  by_cases h : arrowSource b=27
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [35] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_59_35 k]
      exact normal_mem k 135
  · rw [show a k b*normalRep k 59=0 from arrow_incompatible k b 12 27 [12] (normal_endpoints 59) h]
    exact Submodule.zero_mem _
lemma extension_60_49 : a k 49*normalRep k 60=normalRep k 136 := by
  exact (walk_snoc k 13 [13] 49).symm
lemma arrow_span_60 (b : Fin 75) : a k b*normalRep k 60 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_60_49 k]
      exact normal_mem k 136
  · rw [show a k b*normalRep k 60=0 from arrow_incompatible k b 13 35 [13] (normal_endpoints 60) h]
    exact Submodule.zero_mem _
lemma extension_61_9 : a k 9*normalRep k 61=normalRep k 137 := by
  exact (walk_snoc k 14 [14] 9).symm
lemma arrow_span_61 (b : Fin 75) : a k b*normalRep k 61 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_61_9 k]
      exact normal_mem k 137
  · rw [show a k b*normalRep k 61=0 from arrow_incompatible k b 14 9 [14] (normal_endpoints 61) h]
    exact Submodule.zero_mem _
lemma extension_62_1 : a k 1*normalRep k 62=normalRep k 138 := by
  exact (walk_snoc k 15 [15] 1).symm
lemma arrow_span_62 (b : Fin 75) : a k b*normalRep k 62 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_62_1 k]
      exact normal_mem k 138
  · rw [show a k b*normalRep k 62=0 from arrow_incompatible k b 15 1 [15] (normal_endpoints 62) h]
    exact Submodule.zero_mem _
lemma extension_63_57 : a k 57*normalRep k 63=normalRep k 139 := by
  exact (walk_snoc k 15 [16] 57).symm
lemma extension_63_58 : a k 58*normalRep k 63=normalRep k 138 := by
  change a k 58*walk k 15 [16]=walk k 15 [15, 1]
  rw [← walk_snoc]
  exact Universal.mul_reduced_7 (a k) (relation_zero k) (e k 15)
lemma extension_63_59 : a k 59*normalRep k 63=0 := by
  change a k 59*walk k 15 [16]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_8 (a k) (relation_zero k) (e k 15)
lemma arrow_span_63 (b : Fin 75) : a k b*normalRep k 63 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_63_57 k]
      exact normal_mem k 139
    · rw [extension_63_58 k]
      exact normal_mem k 138
    · rw [extension_63_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 63=0 from arrow_incompatible k b 15 39 [16] (normal_endpoints 63) h]
    exact Submodule.zero_mem _
lemma extension_64_20 : a k 20*normalRep k 64=0 := by
  change a k 20*walk k 16 [17]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_9 (a k) (relation_zero k) (e k 16)
lemma extension_64_21 : a k 21*normalRep k 64=normalRep k 140 := by
  exact (walk_snoc k 16 [17] 21).symm
lemma arrow_span_64 (b : Fin 75) : a k b*normalRep k 64 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_64_20 k]
      exact Submodule.zero_mem _
    · rw [extension_64_21 k]
      exact normal_mem k 140
  · rw [show a k b*normalRep k 64=0 from arrow_incompatible k b 16 18 [17] (normal_endpoints 64) h]
    exact Submodule.zero_mem _
lemma extension_65_9 : a k 9*normalRep k 65=normalRep k 141 := by
  exact (walk_snoc k 17 [18] 9).symm
lemma arrow_span_65 (b : Fin 75) : a k b*normalRep k 65 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_65_9 k]
      exact normal_mem k 141
  · rw [show a k b*normalRep k 65=0 from arrow_incompatible k b 17 9 [18] (normal_endpoints 65) h]
    exact Submodule.zero_mem _
lemma extension_66_52 : a k 52*normalRep k 66=normalRep k 141 := by
  change a k 52*walk k 17 [19]=walk k 17 [18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_10 (a k) (relation_zero k) (e k 17)
lemma extension_66_53 : a k 53*normalRep k 66=normalRep k 142 := by
  exact (walk_snoc k 17 [19] 53).symm
lemma arrow_span_66 (b : Fin 75) : a k b*normalRep k 66 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_66_52 k]
      exact normal_mem k 141
    · rw [extension_66_53 k]
      exact normal_mem k 142
  · rw [show a k b*normalRep k 66=0 from arrow_incompatible k b 17 37 [19] (normal_endpoints 66) h]
    exact Submodule.zero_mem _
lemma extension_67_30 : a k 30*normalRep k 67=normalRep k 143 := by
  exact (walk_snoc k 18 [20] 30).symm
lemma extension_67_31 : a k 31*normalRep k 67=0 := by
  change a k 31*walk k 18 [20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_11 (a k) (relation_zero k) (e k 18)
lemma arrow_span_67 (b : Fin 75) : a k b*normalRep k 67 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_67_30 k]
      exact normal_mem k 143
    · rw [extension_67_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 67=0 from arrow_incompatible k b 18 24 [20] (normal_endpoints 67) h]
    exact Submodule.zero_mem _
lemma extension_68_69 : a k 69*normalRep k 68=normalRep k 144 := by
  exact (walk_snoc k 18 [21] 69).symm
lemma extension_68_70 : a k 70*normalRep k 68=normalRep k 145 := by
  exact (walk_snoc k 18 [21] 70).symm
lemma extension_68_71 : a k 71*normalRep k 68=0 := by
  change a k 71*walk k 18 [21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_12 (a k) (relation_zero k) (e k 18)
lemma arrow_span_68 (b : Fin 75) : a k b*normalRep k 68 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_68_69 k]
      exact normal_mem k 144
    · rw [extension_68_70 k]
      exact normal_mem k 145
    · rw [extension_68_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 68=0 from arrow_incompatible k b 18 43 [21] (normal_endpoints 68) h]
    exact Submodule.zero_mem _
lemma extension_69_3 : a k 3*normalRep k 69=normalRep k 146 := by
  exact (walk_snoc k 19 [22] 3).symm
lemma arrow_span_69 (b : Fin 75) : a k b*normalRep k 69 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_69_3 k]
      exact normal_mem k 146
  · rw [show a k b*normalRep k 69=0 from arrow_incompatible k b 19 3 [22] (normal_endpoints 69) h]
    exact Submodule.zero_mem _
lemma extension_70_66 : a k 66*normalRep k 70=normalRep k 147 := by
  exact (walk_snoc k 19 [23] 66).symm
lemma extension_70_67 : a k 67*normalRep k 70=0 := by
  change a k 67*walk k 19 [23]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_13 (a k) (relation_zero k) (e k 19)
lemma extension_70_68 : a k 68*normalRep k 70=(-normalRep k 146) := by
  change a k 68*walk k 19 [23]=(-walk k 19 [22, 3])
  rw [← walk_snoc]
  exact Universal.mul_reduced_14 (a k) (relation_zero k) (e k 19)
lemma arrow_span_70 (b : Fin 75) : a k b*normalRep k 70 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_70_66 k]
      exact normal_mem k 147
    · rw [extension_70_67 k]
      exact Submodule.zero_mem _
    · rw [extension_70_68 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 146)
  · rw [show a k b*normalRep k 70=0 from arrow_incompatible k b 19 42 [23] (normal_endpoints 70) h]
    exact Submodule.zero_mem _
lemma extension_71_18 : a k 18*normalRep k 71=normalRep k 148 := by
  exact (walk_snoc k 20 [24] 18).symm
lemma extension_71_19 : a k 19*normalRep k 71=normalRep k 149 := by
  exact (walk_snoc k 20 [24] 19).symm
lemma arrow_span_71 (b : Fin 75) : a k b*normalRep k 71 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_71_18 k]
      exact normal_mem k 148
    · rw [extension_71_19 k]
      exact normal_mem k 149
  · rw [show a k b*normalRep k 71=0 from arrow_incompatible k b 20 17 [24] (normal_endpoints 71) h]
    exact Submodule.zero_mem _
lemma extension_72_60 : a k 60*normalRep k 72=normalRep k 150 := by
  exact (walk_snoc k 20 [25] 60).symm
lemma extension_72_61 : a k 61*normalRep k 72=0 := by
  change a k 61*walk k 20 [25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_15 (a k) (relation_zero k) (e k 20)
lemma extension_72_62 : a k 62*normalRep k 72=normalRep k 149 := by
  change a k 62*walk k 20 [25]=walk k 20 [24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_16 (a k) (relation_zero k) (e k 20)
lemma arrow_span_72 (b : Fin 75) : a k b*normalRep k 72 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_72_60 k]
      exact normal_mem k 150
    · rw [extension_72_61 k]
      exact Submodule.zero_mem _
    · rw [extension_72_62 k]
      exact normal_mem k 149
  · rw [show a k b*normalRep k 72=0 from arrow_incompatible k b 20 40 [25] (normal_endpoints 72) h]
    exact Submodule.zero_mem _
lemma extension_73_30 : a k 30*normalRep k 73=0 := by
  change a k 30*walk k 21 [26]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_17 (a k) (relation_zero k) (e k 21)
lemma extension_73_31 : a k 31*normalRep k 73=normalRep k 151 := by
  exact (walk_snoc k 21 [26] 31).symm
lemma arrow_span_73 (b : Fin 75) : a k b*normalRep k 73 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_73_30 k]
      exact Submodule.zero_mem _
    · rw [extension_73_31 k]
      exact normal_mem k 151
  · rw [show a k b*normalRep k 73=0 from arrow_incompatible k b 21 24 [26] (normal_endpoints 73) h]
    exact Submodule.zero_mem _
lemma extension_74_57 : a k 57*normalRep k 74=0 := by
  change a k 57*walk k 22 [27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_18 (a k) (relation_zero k) (e k 22)
lemma extension_74_58 : a k 58*normalRep k 74=normalRep k 152 := by
  exact (walk_snoc k 22 [27] 58).symm
lemma extension_74_59 : a k 59*normalRep k 74=normalRep k 153 := by
  exact (walk_snoc k 22 [27] 59).symm
lemma arrow_span_74 (b : Fin 75) : a k b*normalRep k 74 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_74_57 k]
      exact Submodule.zero_mem _
    · rw [extension_74_58 k]
      exact normal_mem k 152
    · rw [extension_74_59 k]
      exact normal_mem k 153
  · rw [show a k b*normalRep k 74=0 from arrow_incompatible k b 22 39 [27] (normal_endpoints 74) h]
    exact Submodule.zero_mem _
lemma extension_75_14 : a k 14*normalRep k 75=normalRep k 154 := by
  exact (walk_snoc k 23 [28] 14).symm
lemma arrow_span_75 (b : Fin 75) : a k b*normalRep k 75 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_75_14 k]
      exact normal_mem k 154
  · rw [show a k b*normalRep k 75=0 from arrow_incompatible k b 23 14 [28] (normal_endpoints 75) h]
    exact Submodule.zero_mem _
lemma extension_76_18 : a k 18*normalRep k 76=normalRep k 154 := by
  change a k 18*walk k 23 [29]=walk k 23 [28, 14]
  rw [← walk_snoc]
  exact Universal.mul_reduced_19 (a k) (relation_zero k) (e k 23)
lemma extension_76_19 : a k 19*normalRep k 76=normalRep k 155 := by
  exact (walk_snoc k 23 [29] 19).symm
lemma arrow_span_76 (b : Fin 75) : a k b*normalRep k 76 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_76_18 k]
      exact normal_mem k 154
    · rw [extension_76_19 k]
      exact normal_mem k 155
  · rw [show a k b*normalRep k 76=0 from arrow_incompatible k b 23 17 [29] (normal_endpoints 76) h]
    exact Submodule.zero_mem _
lemma extension_77_2 : a k 2*normalRep k 77=normalRep k 156 := by
  exact (walk_snoc k 24 [30] 2).symm
lemma arrow_span_77 (b : Fin 75) : a k b*normalRep k 77 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_77_2 k]
      exact normal_mem k 156
  · rw [show a k b*normalRep k 77=0 from arrow_incompatible k b 24 2 [30] (normal_endpoints 77) h]
    exact Submodule.zero_mem _
lemma extension_78_72 : a k 72*normalRep k 78=0 := by
  change a k 72*walk k 24 [31]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_20 (a k) (relation_zero k) (e k 24)
lemma extension_78_73 : a k 73*normalRep k 78=normalRep k 157 := by
  exact (walk_snoc k 24 [31] 73).symm
lemma arrow_span_78 (b : Fin 75) : a k b*normalRep k 78 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_78_72 k]
      exact Submodule.zero_mem _
    · rw [extension_78_73 k]
      exact normal_mem k 157
  · rw [show a k b*normalRep k 78=0 from arrow_incompatible k b 24 44 [31] (normal_endpoints 78) h]
    exact Submodule.zero_mem _
lemma extension_79_60 : a k 60*normalRep k 79=0 := by
  change a k 60*walk k 25 [32]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_21 (a k) (relation_zero k) (e k 25)
lemma extension_79_61 : a k 61*normalRep k 79=normalRep k 158 := by
  exact (walk_snoc k 25 [32] 61).symm
lemma extension_79_62 : a k 62*normalRep k 79=normalRep k 159 := by
  exact (walk_snoc k 25 [32] 62).symm
lemma arrow_span_79 (b : Fin 75) : a k b*normalRep k 79 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_79_60 k]
      exact Submodule.zero_mem _
    · rw [extension_79_61 k]
      exact normal_mem k 158
    · rw [extension_79_62 k]
      exact normal_mem k 159
  · rw [show a k b*normalRep k 79=0 from arrow_incompatible k b 25 40 [32] (normal_endpoints 79) h]
    exact Submodule.zero_mem _
lemma extension_80_13 : a k 13*normalRep k 80=normalRep k 160 := by
  exact (walk_snoc k 26 [33] 13).symm
lemma arrow_span_80 (b : Fin 75) : a k b*normalRep k 80 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_80_13 k]
      exact normal_mem k 160
  · rw [show a k b*normalRep k 80=0 from arrow_incompatible k b 26 13 [33] (normal_endpoints 80) h]
    exact Submodule.zero_mem _
lemma extension_81_63 : a k 63*normalRep k 81=normalRep k 161 := by
  exact (walk_snoc k 26 [34] 63).symm
lemma extension_81_64 : a k 64*normalRep k 81=normalRep k 162 := by
  exact (walk_snoc k 26 [34] 64).symm
lemma extension_81_65 : a k 65*normalRep k 81=normalRep k 160 := by
  change a k 65*walk k 26 [34]=walk k 26 [33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_22 (a k) (relation_zero k) (e k 26)
lemma arrow_span_81 (b : Fin 75) : a k b*normalRep k 81 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_81_63 k]
      exact normal_mem k 161
    · rw [extension_81_64 k]
      exact normal_mem k 162
    · rw [extension_81_65 k]
      exact normal_mem k 160
  · rw [show a k b*normalRep k 81=0 from arrow_incompatible k b 26 41 [34] (normal_endpoints 81) h]
    exact Submodule.zero_mem _
lemma extension_82_54 : a k 54*normalRep k 82=0 := by
  change a k 54*walk k 27 [35]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_23 (a k) (relation_zero k) (e k 27)
lemma extension_82_55 : a k 55*normalRep k 82=normalRep k 163 := by
  exact (walk_snoc k 27 [35] 55).symm
lemma extension_82_56 : a k 56*normalRep k 82=normalRep k 164 := by
  exact (walk_snoc k 27 [35] 56).symm
lemma arrow_span_82 (b : Fin 75) : a k b*normalRep k 82 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_82_54 k]
      exact Submodule.zero_mem _
    · rw [extension_82_55 k]
      exact normal_mem k 163
    · rw [extension_82_56 k]
      exact normal_mem k 164
  · rw [show a k b*normalRep k 82=0 from arrow_incompatible k b 27 38 [35] (normal_endpoints 82) h]
    exact Submodule.zero_mem _
lemma extension_83_69 : a k 69*normalRep k 83=0 := by
  change a k 69*walk k 28 [36]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_24 (a k) (relation_zero k) (e k 28)
lemma extension_83_70 : a k 70*normalRep k 83=normalRep k 165 := by
  exact (walk_snoc k 28 [36] 70).symm
lemma extension_83_71 : a k 71*normalRep k 83=normalRep k 166 := by
  exact (walk_snoc k 28 [36] 71).symm
lemma arrow_span_83 (b : Fin 75) : a k b*normalRep k 83 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_83_69 k]
      exact Submodule.zero_mem _
    · rw [extension_83_70 k]
      exact normal_mem k 165
    · rw [extension_83_71 k]
      exact normal_mem k 166
  · rw [show a k b*normalRep k 83=0 from arrow_incompatible k b 28 43 [36] (normal_endpoints 83) h]
    exact Submodule.zero_mem _
lemma extension_84_24 : a k 24*normalRep k 84=normalRep k 167 := by
  exact (walk_snoc k 29 [37] 24).symm
lemma extension_84_25 : a k 25*normalRep k 84=normalRep k 168 := by
  exact (walk_snoc k 29 [37] 25).symm
lemma arrow_span_84 (b : Fin 75) : a k b*normalRep k 84 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_84_24 k]
      exact normal_mem k 167
    · rw [extension_84_25 k]
      exact normal_mem k 168
  · rw [show a k b*normalRep k 84=0 from arrow_incompatible k b 29 20 [37] (normal_endpoints 84) h]
    exact Submodule.zero_mem _
lemma extension_85_28 : a k 28*normalRep k 85=normalRep k 169 := by
  exact (walk_snoc k 29 [38] 28).symm
lemma extension_85_29 : a k 29*normalRep k 85=normalRep k 167 := by
  change a k 29*walk k 29 [38]=walk k 29 [37, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_25 (a k) (relation_zero k) (e k 29)
lemma arrow_span_85 (b : Fin 75) : a k b*normalRep k 85 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_85_28 k]
      exact normal_mem k 169
    · rw [extension_85_29 k]
      exact normal_mem k 167
  · rw [show a k b*normalRep k 85=0 from arrow_incompatible k b 29 23 [38] (normal_endpoints 85) h]
    exact Submodule.zero_mem _
lemma extension_86_12 : a k 12*normalRep k 86=normalRep k 170 := by
  exact (walk_snoc k 30 [39] 12).symm
lemma arrow_span_86 (b : Fin 75) : a k b*normalRep k 86 ∈ normalSpan k := by
  by_cases h : arrowSource b=12
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [12] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_86_12 k]
      exact normal_mem k 170
  · rw [show a k b*normalRep k 86=0 from arrow_incompatible k b 30 12 [39] (normal_endpoints 86) h]
    exact Submodule.zero_mem _
lemma extension_87_60 : a k 60*normalRep k 87=normalRep k 171 := by
  exact (walk_snoc k 30 [40] 60).symm
lemma extension_87_61 : a k 61*normalRep k 87=normalRep k 170 := by
  change a k 61*walk k 30 [40]=walk k 30 [39, 12]
  rw [← walk_snoc]
  exact Universal.mul_reduced_26 (a k) (relation_zero k) (e k 30)
lemma extension_87_62 : a k 62*normalRep k 87=normalRep k 172 := by
  exact (walk_snoc k 30 [40] 62).symm
lemma arrow_span_87 (b : Fin 75) : a k b*normalRep k 87 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_87_60 k]
      exact normal_mem k 171
    · rw [extension_87_61 k]
      exact normal_mem k 170
    · rw [extension_87_62 k]
      exact normal_mem k 172
  · rw [show a k b*normalRep k 87=0 from arrow_incompatible k b 30 40 [40] (normal_endpoints 87) h]
    exact Submodule.zero_mem _
lemma extension_88_43 : a k 43*normalRep k 88=normalRep k 173 := by
  exact (walk_snoc k 31 [41] 43).symm
lemma extension_88_44 : a k 44*normalRep k 88=normalRep k 174 := by
  exact (walk_snoc k 31 [41] 44).symm
lemma arrow_span_88 (b : Fin 75) : a k b*normalRep k 88 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_88_43 k]
      exact normal_mem k 173
    · rw [extension_88_44 k]
      exact normal_mem k 174
  · rw [show a k b*normalRep k 88=0 from arrow_incompatible k b 31 32 [41] (normal_endpoints 88) h]
    exact Submodule.zero_mem _
lemma extension_89_45 : a k 45*normalRep k 89=normalRep k 175 := by
  exact (walk_snoc k 31 [42] 45).symm
lemma extension_89_46 : a k 46*normalRep k 89=normalRep k 173 := by
  change a k 46*walk k 31 [42]=walk k 31 [41, 43]
  rw [← walk_snoc]
  exact Universal.mul_reduced_27 (a k) (relation_zero k) (e k 31)
lemma arrow_span_89 (b : Fin 75) : a k b*normalRep k 89 ∈ normalSpan k := by
  by_cases h : arrowSource b=33
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [45, 46] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_89_45 k]
      exact normal_mem k 175
    · rw [extension_89_46 k]
      exact normal_mem k 173
  · rw [show a k b*normalRep k 89=0 from arrow_incompatible k b 31 33 [42] (normal_endpoints 89) h]
    exact Submodule.zero_mem _
lemma extension_90_47 : a k 47*normalRep k 90=normalRep k 176 := by
  exact (walk_snoc k 32 [43] 47).symm
lemma extension_90_48 : a k 48*normalRep k 90=normalRep k 177 := by
  exact (walk_snoc k 32 [43] 48).symm
lemma arrow_span_90 (b : Fin 75) : a k b*normalRep k 90 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_90_47 k]
      exact normal_mem k 176
    · rw [extension_90_48 k]
      exact normal_mem k 177
  · rw [show a k b*normalRep k 90=0 from arrow_incompatible k b 32 34 [43] (normal_endpoints 90) h]
    exact Submodule.zero_mem _
lemma extension_91_57 : a k 57*normalRep k 91=normalRep k 178 := by
  exact (walk_snoc k 32 [44] 57).symm
lemma extension_91_58 : a k 58*normalRep k 91=normalRep k 179 := by
  exact (walk_snoc k 32 [44] 58).symm
lemma extension_91_59 : a k 59*normalRep k 91=normalRep k 177 := by
  change a k 59*walk k 32 [44]=walk k 32 [43, 48]
  rw [← walk_snoc]
  exact Universal.mul_reduced_28 (a k) (relation_zero k) (e k 32)
lemma arrow_span_91 (b : Fin 75) : a k b*normalRep k 91 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_91_57 k]
      exact normal_mem k 178
    · rw [extension_91_58 k]
      exact normal_mem k 179
    · rw [extension_91_59 k]
      exact normal_mem k 177
  · rw [show a k b*normalRep k 91=0 from arrow_incompatible k b 32 39 [44] (normal_endpoints 91) h]
    exact Submodule.zero_mem _
lemma extension_92_6 : a k 6*normalRep k 92=normalRep k 180 := by
  exact (walk_snoc k 33 [45] 6).symm
lemma arrow_span_92 (b : Fin 75) : a k b*normalRep k 92 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_92_6 k]
      exact normal_mem k 180
  · rw [show a k b*normalRep k 92=0 from arrow_incompatible k b 33 6 [45] (normal_endpoints 92) h]
    exact Submodule.zero_mem _
lemma extension_93_47 : a k 47*normalRep k 93=normalRep k 180 := by
  change a k 47*walk k 33 [46]=walk k 33 [45, 6]
  rw [← walk_snoc]
  exact Universal.mul_reduced_29 (a k) (relation_zero k) (e k 33)
lemma extension_93_48 : a k 48*normalRep k 93=normalRep k 181 := by
  exact (walk_snoc k 33 [46] 48).symm
lemma arrow_span_93 (b : Fin 75) : a k b*normalRep k 93 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_93_47 k]
      exact normal_mem k 180
    · rw [extension_93_48 k]
      exact normal_mem k 181
  · rw [show a k b*normalRep k 93=0 from arrow_incompatible k b 33 34 [46] (normal_endpoints 93) h]
    exact Submodule.zero_mem _
lemma extension_94_7 : a k 7*normalRep k 94=normalRep k 182 := by
  exact (walk_snoc k 34 [47] 7).symm
lemma arrow_span_94 (b : Fin 75) : a k b*normalRep k 94 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_94_7 k]
      exact normal_mem k 182
  · rw [show a k b*normalRep k 94=0 from arrow_incompatible k b 34 7 [47] (normal_endpoints 94) h]
    exact Submodule.zero_mem _
lemma extension_95_50 : a k 50*normalRep k 95=normalRep k 182 := by
  change a k 50*walk k 34 [48]=walk k 34 [47, 7]
  rw [← walk_snoc]
  exact Universal.mul_reduced_30 (a k) (relation_zero k) (e k 34)
lemma extension_95_51 : a k 51*normalRep k 95=normalRep k 183 := by
  exact (walk_snoc k 34 [48] 51).symm
lemma arrow_span_95 (b : Fin 75) : a k b*normalRep k 95 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_95_50 k]
      exact normal_mem k 182
    · rw [extension_95_51 k]
      exact normal_mem k 183
  · rw [show a k b*normalRep k 95=0 from arrow_incompatible k b 34 36 [48] (normal_endpoints 95) h]
    exact Submodule.zero_mem _
lemma extension_96_69 : a k 69*normalRep k 96=normalRep k 184 := by
  exact (walk_snoc k 35 [49] 69).symm
lemma extension_96_70 : a k 70*normalRep k 96=0 := by
  change a k 70*walk k 35 [49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_31 (a k) (relation_zero k) (e k 35)
lemma extension_96_71 : a k 71*normalRep k 96=normalRep k 185 := by
  exact (walk_snoc k 35 [49] 71).symm
lemma arrow_span_96 (b : Fin 75) : a k b*normalRep k 96 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_96_69 k]
      exact normal_mem k 184
    · rw [extension_96_70 k]
      exact Submodule.zero_mem _
    · rw [extension_96_71 k]
      exact normal_mem k 185
  · rw [show a k b*normalRep k 96=0 from arrow_incompatible k b 35 43 [49] (normal_endpoints 96) h]
    exact Submodule.zero_mem _
lemma extension_97_17 : a k 17*normalRep k 97=normalRep k 186 := by
  exact (walk_snoc k 36 [50] 17).symm
lemma arrow_span_97 (b : Fin 75) : a k b*normalRep k 97 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_97_17 k]
      exact normal_mem k 186
  · rw [show a k b*normalRep k 97=0 from arrow_incompatible k b 36 16 [50] (normal_endpoints 97) h]
    exact Submodule.zero_mem _
lemma extension_98_63 : a k 63*normalRep k 98=normalRep k 186 := by
  change a k 63*walk k 36 [51]=walk k 36 [50, 17]
  rw [← walk_snoc]
  exact Universal.mul_reduced_32 (a k) (relation_zero k) (e k 36)
lemma extension_98_64 : a k 64*normalRep k 98=normalRep k 187 := by
  exact (walk_snoc k 36 [51] 64).symm
lemma extension_98_65 : a k 65*normalRep k 98=normalRep k 188 := by
  exact (walk_snoc k 36 [51] 65).symm
lemma arrow_span_98 (b : Fin 75) : a k b*normalRep k 98 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_98_63 k]
      exact normal_mem k 186
    · rw [extension_98_64 k]
      exact normal_mem k 187
    · rw [extension_98_65 k]
      exact normal_mem k 188
  · rw [show a k b*normalRep k 98=0 from arrow_incompatible k b 36 41 [51] (normal_endpoints 98) h]
    exact Submodule.zero_mem _
lemma extension_99_41 : a k 41*normalRep k 99=normalRep k 189 := by
  exact (walk_snoc k 37 [52] 41).symm
lemma extension_99_42 : a k 42*normalRep k 99=normalRep k 190 := by
  exact (walk_snoc k 37 [52] 42).symm
lemma arrow_span_99 (b : Fin 75) : a k b*normalRep k 99 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_99_41 k]
      exact normal_mem k 189
    · rw [extension_99_42 k]
      exact normal_mem k 190
  · rw [show a k b*normalRep k 99=0 from arrow_incompatible k b 37 31 [52] (normal_endpoints 99) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
