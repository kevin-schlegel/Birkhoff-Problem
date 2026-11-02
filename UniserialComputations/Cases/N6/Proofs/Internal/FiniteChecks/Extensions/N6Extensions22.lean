import N6NormalData
import N6Reduced14
import N6Reduced15
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_1100_28 : a k 28*normalRep k 1100=normalRep k 1185 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_1100_29 : a k 29*normalRep k 1100=normalRep k 1183 := by
  change a k 29*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]=walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_929 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1100 (b : Fin 75) : a k b*normalRep k 1100 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1100_28 k]
      exact normal_mem k 1185
    · rw [extension_1100_29 k]
      exact normal_mem k 1183
  · rw [show a k b*normalRep k 1100=0 from arrow_incompatible k b 12 23 [12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 1100) h]
    exact Submodule.zero_mem _
lemma extension_1101_5 : a k 5*normalRep k 1101=normalRep k 1186 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1101 (b : Fin 75) : a k b*normalRep k 1101 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1101_5 k]
      exact normal_mem k 1186
  · rw [show a k b*normalRep k 1101=0 from arrow_incompatible k b 13 5 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1101) h]
    exact Submodule.zero_mem _
lemma extension_1102_33 : a k 33*normalRep k 1102=0 := by
  change a k 33*walk k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_883 (a k) (relation_zero k) (e k 13)
lemma extension_1102_34 : a k 34*normalRep k 1102=normalRep k 1186 := by
  change a k 34*walk k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_945 (a k) (relation_zero k) (e k 13)
lemma arrow_span_1102 (b : Fin 75) : a k b*normalRep k 1102 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1102_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1102_34 k]
      exact normal_mem k 1186
  · rw [show a k b*normalRep k 1102=0 from arrow_incompatible k b 13 26 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1102) h]
    exact Submodule.zero_mem _
lemma arrow_span_1103 (b : Fin 75) : a k b*normalRep k 1103 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1103=0 from arrow_incompatible k b 14 46 [14, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1103) h]
    exact Submodule.zero_mem _
lemma extension_1104_5 : a k 5*normalRep k 1104=normalRep k 1187 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1104 (b : Fin 75) : a k b*normalRep k 1104 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1104_5 k]
      exact normal_mem k 1187
  · rw [show a k b*normalRep k 1104=0 from arrow_incompatible k b 16 5 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1104) h]
    exact Submodule.zero_mem _
lemma extension_1105_33 : a k 33*normalRep k 1105=0 := by
  change a k 33*walk k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_884 (a k) (relation_zero k) (e k 16)
lemma extension_1105_34 : a k 34*normalRep k 1105=normalRep k 1187 := by
  change a k 34*walk k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_946 (a k) (relation_zero k) (e k 16)
lemma arrow_span_1105 (b : Fin 75) : a k b*normalRep k 1105 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1105_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1105_34 k]
      exact normal_mem k 1187
  · rw [show a k b*normalRep k 1105=0 from arrow_incompatible k b 16 26 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1105) h]
    exact Submodule.zero_mem _
lemma arrow_span_1106 (b : Fin 75) : a k b*normalRep k 1106 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1106=0 from arrow_incompatible k b 17 46 [18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1106) h]
    exact Submodule.zero_mem _
lemma extension_1107_63 : a k 63*normalRep k 1107=normalRep k 1188 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1107_64 : a k 64*normalRep k 1107=0 := by
  change a k 64*walk k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_886 (a k) (relation_zero k) (e k 18)
lemma extension_1107_65 : a k 65*normalRep k 1107=0 := by
  change a k 65*walk k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_900 (a k) (relation_zero k) (e k 18)
lemma arrow_span_1107 (b : Fin 75) : a k b*normalRep k 1107 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1107_63 k]
      exact normal_mem k 1188
    · rw [extension_1107_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1107_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1107=0 from arrow_incompatible k b 18 41 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1107) h]
    exact Submodule.zero_mem _
lemma extension_1108_30 : a k 30*normalRep k 1108=normalRep k 1189 := by
  exact (walk_snoc k 19 [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20] 30).symm
lemma extension_1108_31 : a k 31*normalRep k 1108=0 := by
  change a k 31*walk k 19 [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_915 (a k) (relation_zero k) (e k 19)
lemma arrow_span_1108 (b : Fin 75) : a k b*normalRep k 1108 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1108_30 k]
      exact normal_mem k 1189
    · rw [extension_1108_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1108=0 from arrow_incompatible k b 19 24 [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20] (normal_endpoints 1108) h]
    exact Submodule.zero_mem _
lemma extension_1109_0 : a k 0*normalRep k 1109=normalRep k 1190 := by
  exact (walk_snoc k 20 [24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1109 (b : Fin 75) : a k b*normalRep k 1109 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1109_0 k]
      exact normal_mem k 1190
  · rw [show a k b*normalRep k 1109=0 from arrow_incompatible k b 20 0 [24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1109) h]
    exact Submodule.zero_mem _
lemma extension_1110_13 : a k 13*normalRep k 1110=normalRep k 1191 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33] 13).symm
lemma arrow_span_1110 (b : Fin 75) : a k b*normalRep k 1110 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1110_13 k]
      exact normal_mem k 1191
  · rw [show a k b*normalRep k 1110=0 from arrow_incompatible k b 21 13 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33] (normal_endpoints 1110) h]
    exact Submodule.zero_mem _
lemma extension_1111_63 : a k 63*normalRep k 1111=normalRep k 1192 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] 63).symm
lemma extension_1111_64 : a k 64*normalRep k 1111=normalRep k 1193 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] 64).symm
lemma extension_1111_65 : a k 65*normalRep k 1111=normalRep k 1191 := by
  change a k 65*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_927 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1111 (b : Fin 75) : a k b*normalRep k 1111 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1111_63 k]
      exact normal_mem k 1192
    · rw [extension_1111_64 k]
      exact normal_mem k 1193
    · rw [extension_1111_65 k]
      exact normal_mem k 1191
  · rw [show a k b*normalRep k 1111=0 from arrow_incompatible k b 21 41 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] (normal_endpoints 1111) h]
    exact Submodule.zero_mem _
lemma extension_1112_17 : a k 17*normalRep k 1112=normalRep k 1192 := by
  change a k 17*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_936 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1112 (b : Fin 75) : a k b*normalRep k 1112 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1112_17 k]
      exact normal_mem k 1192
  · rw [show a k b*normalRep k 1112=0 from arrow_incompatible k b 21 16 [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50] (normal_endpoints 1112) h]
    exact Submodule.zero_mem _
lemma extension_1113_41 : a k 41*normalRep k 1113=normalRep k 1194 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1113_42 : a k 42*normalRep k 1113=0 := by
  change a k 42*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_891 (a k) (relation_zero k) (e k 22)
lemma arrow_span_1113 (b : Fin 75) : a k b*normalRep k 1113 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1113_41 k]
      exact normal_mem k 1194
    · rw [extension_1113_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1113=0 from arrow_incompatible k b 22 31 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1113) h]
    exact Submodule.zero_mem _
lemma extension_1114_54 : a k 54*normalRep k 1114=normalRep k 1195 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1114_55 : a k 55*normalRep k 1114=0 := by
  change a k 55*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_894 (a k) (relation_zero k) (e k 22)
lemma extension_1114_56 : a k 56*normalRep k 1114=normalRep k 1194 := by
  change a k 56*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_937 (a k) (relation_zero k) (e k 22)
lemma arrow_span_1114 (b : Fin 75) : a k b*normalRep k 1114 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1114_54 k]
      exact normal_mem k 1195
    · rw [extension_1114_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1114_56 k]
      exact normal_mem k 1194
  · rw [show a k b*normalRep k 1114=0 from arrow_incompatible k b 22 38 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1114) h]
    exact Submodule.zero_mem _
lemma extension_1115_0 : a k 0*normalRep k 1115=normalRep k 1196 := by
  exact (walk_snoc k 23 [28, 14, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1115 (b : Fin 75) : a k b*normalRep k 1115 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1115_0 k]
      exact normal_mem k 1196
  · rw [show a k b*normalRep k 1115=0 from arrow_incompatible k b 23 0 [28, 14, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1115) h]
    exact Submodule.zero_mem _
lemma extension_1116_49 : a k 49*normalRep k 1116=normalRep k 1197 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] 49).symm
lemma arrow_span_1116 (b : Fin 75) : a k b*normalRep k 1116 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1116_49 k]
      exact normal_mem k 1197
  · rw [show a k b*normalRep k 1116=0 from arrow_incompatible k b 24 35 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] (normal_endpoints 1116) h]
    exact Submodule.zero_mem _
lemma extension_1117_20 : a k 20*normalRep k 1117=0 := by
  change a k 20*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_911 (a k) (relation_zero k) (e k 24)
lemma extension_1117_21 : a k 21*normalRep k 1117=normalRep k 1198 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] 21).symm
lemma arrow_span_1117 (b : Fin 75) : a k b*normalRep k 1117 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1117_20 k]
      exact Submodule.zero_mem _
    · rw [extension_1117_21 k]
      exact normal_mem k 1198
  · rw [show a k b*normalRep k 1117=0 from arrow_incompatible k b 24 18 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] (normal_endpoints 1117) h]
    exact Submodule.zero_mem _
lemma extension_1118_36 : a k 36*normalRep k 1118=normalRep k 1198 + normalRep k 1197 := by
  change a k 36*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_950 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1118 (b : Fin 75) : a k b*normalRep k 1118 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1118_36 k]
      exact (normalSpan k).add_mem (normal_mem k 1198) (normal_mem k 1197)
  · rw [show a k b*normalRep k 1118=0 from arrow_incompatible k b 24 28 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64] (normal_endpoints 1118) h]
    exact Submodule.zero_mem _
lemma extension_1119_66 : a k 66*normalRep k 1119=normalRep k 1199 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_1119_67 : a k 67*normalRep k 1119=0 := by
  change a k 67*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_903 (a k) (relation_zero k) (e k 25)
lemma extension_1119_68 : a k 68*normalRep k 1119=normalRep k 1200 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_1119 (b : Fin 75) : a k b*normalRep k 1119 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1119_66 k]
      exact normal_mem k 1199
    · rw [extension_1119_67 k]
      exact Submodule.zero_mem _
    · rw [extension_1119_68 k]
      exact normal_mem k 1200
  · rw [show a k b*normalRep k 1119=0 from arrow_incompatible k b 25 42 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] (normal_endpoints 1119) h]
    exact Submodule.zero_mem _
lemma extension_1120_37 : a k 37*normalRep k 1120=normalRep k 1199 := by
  change a k 37*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72]=walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_957 (a k) (relation_zero k) (e k 25)
lemma extension_1120_38 : a k 38*normalRep k 1120=normalRep k 1201 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_1120 (b : Fin 75) : a k b*normalRep k 1120 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1120_37 k]
      exact normal_mem k 1199
    · rw [extension_1120_38 k]
      exact normal_mem k 1201
  · rw [show a k b*normalRep k 1120=0 from arrow_incompatible k b 25 29 [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] (normal_endpoints 1120) h]
    exact Submodule.zero_mem _
lemma extension_1121_3 : a k 3*normalRep k 1121=(-normalRep k 1200) := by
  change a k 3*walk k 25 [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22]=(-walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_918 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1121 (b : Fin 75) : a k b*normalRep k 1121 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1121_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1200)
  · rw [show a k b*normalRep k 1121=0 from arrow_incompatible k b 25 3 [32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22] (normal_endpoints 1121) h]
    exact Submodule.zero_mem _
lemma extension_1122_57 : a k 57*normalRep k 1122=normalRep k 1202 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1122_58 : a k 58*normalRep k 1122=normalRep k 1203 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1122_59 : a k 59*normalRep k 1122=0 := by
  change a k 59*walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_909 (a k) (relation_zero k) (e k 26)
lemma arrow_span_1122 (b : Fin 75) : a k b*normalRep k 1122 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1122_57 k]
      exact normal_mem k 1202
    · rw [extension_1122_58 k]
      exact normal_mem k 1203
    · rw [extension_1122_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1122=0 from arrow_incompatible k b 26 39 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1122) h]
    exact Submodule.zero_mem _
lemma extension_1123_1 : a k 1*normalRep k 1123=normalRep k 1203 := by
  change a k 1*walk k 26 [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_906 (a k) (relation_zero k) (e k 26)
lemma arrow_span_1123 (b : Fin 75) : a k b*normalRep k 1123 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1123_1 k]
      exact normal_mem k 1203
  · rw [show a k b*normalRep k 1123=0 from arrow_incompatible k b 26 1 [33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1123) h]
    exact Submodule.zero_mem _
lemma extension_1124_18 : a k 18*normalRep k 1124=normalRep k 1204 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_1124_19 : a k 19*normalRep k 1124=normalRep k 1205 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_1124 (b : Fin 75) : a k b*normalRep k 1124 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1124_18 k]
      exact normal_mem k 1204
    · rw [extension_1124_19 k]
      exact normal_mem k 1205
  · rw [show a k b*normalRep k 1124=0 from arrow_incompatible k b 27 17 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 1124) h]
    exact Submodule.zero_mem _
lemma extension_1125_60 : a k 60*normalRep k 1125=normalRep k 1206 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_1125_61 : a k 61*normalRep k 1125=0 := by
  change a k 61*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_920 (a k) (relation_zero k) (e k 27)
lemma extension_1125_62 : a k 62*normalRep k 1125=normalRep k 1205 := by
  change a k 62*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_922 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1125 (b : Fin 75) : a k b*normalRep k 1125 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1125_60 k]
      exact normal_mem k 1206
    · rw [extension_1125_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1125_62 k]
      exact normal_mem k 1205
  · rw [show a k b*normalRep k 1125=0 from arrow_incompatible k b 27 40 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 1125) h]
    exact Submodule.zero_mem _
lemma extension_1126_14 : a k 14*normalRep k 1126=normalRep k 1204 := by
  change a k 14*walk k 27 [35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_925 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1126 (b : Fin 75) : a k b*normalRep k 1126 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1126_14 k]
      exact normal_mem k 1204
  · rw [show a k b*normalRep k 1126=0 from arrow_incompatible k b 27 14 [35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 1126) h]
    exact Submodule.zero_mem _
lemma extension_1127_63 : a k 63*normalRep k 1127=normalRep k 1207 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34] 63).symm
lemma extension_1127_64 : a k 64*normalRep k 1127=0 := by
  change a k 64*walk k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_887 (a k) (relation_zero k) (e k 28)
lemma extension_1127_65 : a k 65*normalRep k 1127=0 := by
  change a k 65*walk k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_901 (a k) (relation_zero k) (e k 28)
lemma arrow_span_1127 (b : Fin 75) : a k b*normalRep k 1127 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1127_63 k]
      exact normal_mem k 1207
    · rw [extension_1127_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1127_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1127=0 from arrow_incompatible k b 28 41 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34] (normal_endpoints 1127) h]
    exact Submodule.zero_mem _
lemma extension_1128_2 : a k 2*normalRep k 1128=normalRep k 1208 := by
  exact (walk_snoc k 29 [37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1128 (b : Fin 75) : a k b*normalRep k 1128 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1128_2 k]
      exact normal_mem k 1208
  · rw [show a k b*normalRep k 1128=0 from arrow_incompatible k b 29 2 [37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1128) h]
    exact Submodule.zero_mem _
lemma extension_1129_66 : a k 66*normalRep k 1129=normalRep k 1209 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_1129_67 : a k 67*normalRep k 1129=0 := by
  change a k 67*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_904 (a k) (relation_zero k) (e k 30)
lemma extension_1129_68 : a k 68*normalRep k 1129=normalRep k 1210 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_1129 (b : Fin 75) : a k b*normalRep k 1129 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1129_66 k]
      exact normal_mem k 1209
    · rw [extension_1129_67 k]
      exact Submodule.zero_mem _
    · rw [extension_1129_68 k]
      exact normal_mem k 1210
  · rw [show a k b*normalRep k 1129=0 from arrow_incompatible k b 30 42 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8] (normal_endpoints 1129) h]
    exact Submodule.zero_mem _
lemma extension_1130_37 : a k 37*normalRep k 1130=normalRep k 1209 := by
  change a k 37*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72]=walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_958 (a k) (relation_zero k) (e k 30)
lemma extension_1130_38 : a k 38*normalRep k 1130=normalRep k 1211 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_1130 (b : Fin 75) : a k b*normalRep k 1130 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1130_37 k]
      exact normal_mem k 1209
    · rw [extension_1130_38 k]
      exact normal_mem k 1211
  · rw [show a k b*normalRep k 1130=0 from arrow_incompatible k b 30 29 [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72] (normal_endpoints 1130) h]
    exact Submodule.zero_mem _
lemma extension_1131_3 : a k 3*normalRep k 1131=(-normalRep k 1210) := by
  change a k 3*walk k 30 [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 22]=(-walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_919 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1131 (b : Fin 75) : a k b*normalRep k 1131 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1131_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1210)
  · rw [show a k b*normalRep k 1131=0 from arrow_incompatible k b 30 3 [39, 12, 35, 55, 27, 58, 34, 63, 21, 70, 22] (normal_endpoints 1131) h]
    exact Submodule.zero_mem _
lemma extension_1132_0 : a k 0*normalRep k 1132=normalRep k 1212 := by
  exact (walk_snoc k 30 [40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2] 0).symm
lemma arrow_span_1132 (b : Fin 75) : a k b*normalRep k 1132 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1132_0 k]
      exact normal_mem k 1212
  · rw [show a k b*normalRep k 1132=0 from arrow_incompatible k b 30 0 [40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2] (normal_endpoints 1132) h]
    exact Submodule.zero_mem _
lemma extension_1133_9 : a k 9*normalRep k 1133=normalRep k 1213 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1133 (b : Fin 75) : a k b*normalRep k 1133 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1133_9 k]
      exact normal_mem k 1213
  · rw [show a k b*normalRep k 1133=0 from arrow_incompatible k b 31 9 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18] (normal_endpoints 1133) h]
    exact Submodule.zero_mem _
lemma extension_1134_52 : a k 52*normalRep k 1134=normalRep k 1213 := by
  change a k 52*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19]=walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_912 (a k) (relation_zero k) (e k 31)
lemma extension_1134_53 : a k 53*normalRep k 1134=normalRep k 1214 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1134 (b : Fin 75) : a k b*normalRep k 1134 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1134_52 k]
      exact normal_mem k 1213
    · rw [extension_1134_53 k]
      exact normal_mem k 1214
  · rw [show a k b*normalRep k 1134=0 from arrow_incompatible k b 31 37 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19] (normal_endpoints 1134) h]
    exact Submodule.zero_mem _
lemma extension_1135_4 : a k 4*normalRep k 1135=normalRep k 1214 := by
  change a k 4*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60]=walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_948 (a k) (relation_zero k) (e k 31)
lemma arrow_span_1135 (b : Fin 75) : a k b*normalRep k 1135 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1135_4 k]
      exact normal_mem k 1214
  · rw [show a k b*normalRep k 1135=0 from arrow_incompatible k b 31 4 [41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60] (normal_endpoints 1135) h]
    exact Submodule.zero_mem _
lemma extension_1136_41 : a k 41*normalRep k 1136=normalRep k 1215 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1136_42 : a k 42*normalRep k 1136=0 := by
  change a k 42*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_892 (a k) (relation_zero k) (e k 32)
lemma arrow_span_1136 (b : Fin 75) : a k b*normalRep k 1136 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1136_41 k]
      exact normal_mem k 1215
    · rw [extension_1136_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1136=0 from arrow_incompatible k b 32 31 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9] (normal_endpoints 1136) h]
    exact Submodule.zero_mem _
lemma extension_1137_54 : a k 54*normalRep k 1137=normalRep k 1216 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1137_55 : a k 55*normalRep k 1137=0 := by
  change a k 55*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_895 (a k) (relation_zero k) (e k 32)
lemma extension_1137_56 : a k 56*normalRep k 1137=normalRep k 1215 := by
  change a k 56*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]=walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_938 (a k) (relation_zero k) (e k 32)
lemma arrow_span_1137 (b : Fin 75) : a k b*normalRep k 1137 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1137_54 k]
      exact normal_mem k 1216
    · rw [extension_1137_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1137_56 k]
      exact normal_mem k 1215
  · rw [show a k b*normalRep k 1137=0 from arrow_incompatible k b 32 38 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53] (normal_endpoints 1137) h]
    exact Submodule.zero_mem _
lemma extension_1138_41 : a k 41*normalRep k 1138=normalRep k 1217 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1138_42 : a k 42*normalRep k 1138=0 := by
  change a k 42*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_893 (a k) (relation_zero k) (e k 33)
lemma arrow_span_1138 (b : Fin 75) : a k b*normalRep k 1138 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1138_41 k]
      exact normal_mem k 1217
    · rw [extension_1138_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1138=0 from arrow_incompatible k b 33 31 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9] (normal_endpoints 1138) h]
    exact Submodule.zero_mem _
lemma extension_1139_54 : a k 54*normalRep k 1139=normalRep k 1218 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1139_55 : a k 55*normalRep k 1139=0 := by
  change a k 55*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_896 (a k) (relation_zero k) (e k 33)
lemma extension_1139_56 : a k 56*normalRep k 1139=normalRep k 1217 := by
  change a k 56*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53]=walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_939 (a k) (relation_zero k) (e k 33)
lemma arrow_span_1139 (b : Fin 75) : a k b*normalRep k 1139 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1139_54 k]
      exact normal_mem k 1218
    · rw [extension_1139_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1139_56 k]
      exact normal_mem k 1217
  · rw [show a k b*normalRep k 1139=0 from arrow_incompatible k b 33 38 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53] (normal_endpoints 1139) h]
    exact Submodule.zero_mem _
lemma extension_1140_43 : a k 43*normalRep k 1140=0 := by
  change a k 43*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_898 (a k) (relation_zero k) (e k 34)
lemma extension_1140_44 : a k 44*normalRep k 1140=normalRep k 1219 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1140 (b : Fin 75) : a k b*normalRep k 1140 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1140_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1140_44 k]
      exact normal_mem k 1219
  · rw [show a k b*normalRep k 1140=0 from arrow_incompatible k b 34 32 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1140) h]
    exact Submodule.zero_mem _
lemma extension_1141_15 : a k 15*normalRep k 1141=normalRep k 1220 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1141_16 : a k 16*normalRep k 1141=normalRep k 1219 := by
  change a k 16*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]=walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_941 (a k) (relation_zero k) (e k 34)
lemma arrow_span_1141 (b : Fin 75) : a k b*normalRep k 1141 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1141_15 k]
      exact normal_mem k 1220
    · rw [extension_1141_16 k]
      exact normal_mem k 1219
  · rw [show a k b*normalRep k 1141=0 from arrow_incompatible k b 34 15 [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1141) h]
    exact Submodule.zero_mem _
lemma extension_1142_63 : a k 63*normalRep k 1142=normalRep k 1221 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1142_64 : a k 64*normalRep k 1142=0 := by
  change a k 64*walk k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_888 (a k) (relation_zero k) (e k 35)
lemma extension_1142_65 : a k 65*normalRep k 1142=0 := by
  change a k 65*walk k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_902 (a k) (relation_zero k) (e k 35)
lemma arrow_span_1142 (b : Fin 75) : a k b*normalRep k 1142 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1142_63 k]
      exact normal_mem k 1221
    · rw [extension_1142_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1142_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1142=0 from arrow_incompatible k b 35 41 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1142) h]
    exact Submodule.zero_mem _
lemma extension_1143_57 : a k 57*normalRep k 1143=normalRep k 1222 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1143_58 : a k 58*normalRep k 1143=normalRep k 1223 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1143_59 : a k 59*normalRep k 1143=0 := by
  change a k 59*walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_910 (a k) (relation_zero k) (e k 36)
lemma arrow_span_1143 (b : Fin 75) : a k b*normalRep k 1143 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1143_57 k]
      exact normal_mem k 1222
    · rw [extension_1143_58 k]
      exact normal_mem k 1223
    · rw [extension_1143_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1143=0 from arrow_incompatible k b 36 39 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1143) h]
    exact Submodule.zero_mem _
lemma extension_1144_1 : a k 1*normalRep k 1144=normalRep k 1223 := by
  change a k 1*walk k 36 [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_907 (a k) (relation_zero k) (e k 36)
lemma arrow_span_1144 (b : Fin 75) : a k b*normalRep k 1144 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1144_1 k]
      exact normal_mem k 1223
  · rw [show a k b*normalRep k 1144=0 from arrow_incompatible k b 36 1 [50, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1144) h]
    exact Submodule.zero_mem _
lemma extension_1145_18 : a k 18*normalRep k 1145=normalRep k 1224 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24] 18).symm
lemma extension_1145_19 : a k 19*normalRep k 1145=normalRep k 1225 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24] 19).symm
lemma arrow_span_1145 (b : Fin 75) : a k b*normalRep k 1145 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1145_18 k]
      exact normal_mem k 1224
    · rw [extension_1145_19 k]
      exact normal_mem k 1225
  · rw [show a k b*normalRep k 1145=0 from arrow_incompatible k b 37 17 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24] (normal_endpoints 1145) h]
    exact Submodule.zero_mem _
lemma extension_1146_60 : a k 60*normalRep k 1146=normalRep k 1226 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25] 60).symm
lemma extension_1146_61 : a k 61*normalRep k 1146=0 := by
  change a k 61*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_921 (a k) (relation_zero k) (e k 37)
lemma extension_1146_62 : a k 62*normalRep k 1146=normalRep k 1225 := by
  change a k 62*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25]=walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_923 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1146 (b : Fin 75) : a k b*normalRep k 1146 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1146_60 k]
      exact normal_mem k 1226
    · rw [extension_1146_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1146_62 k]
      exact normal_mem k 1225
  · rw [show a k b*normalRep k 1146=0 from arrow_incompatible k b 37 40 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25] (normal_endpoints 1146) h]
    exact Submodule.zero_mem _
lemma extension_1147_14 : a k 14*normalRep k 1147=(-normalRep k 1224) := by
  change a k 14*walk k 37 [52, 41, 43, 48, 51, 64, 36, 71, 72, 38, 28]=(-walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18])
  rw [← walk_snoc]
  exact Universal.mul_reduced_926 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1147 (b : Fin 75) : a k b*normalRep k 1147 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1147_14 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1224)
  · rw [show a k b*normalRep k 1147=0 from arrow_incompatible k b 37 14 [52, 41, 43, 48, 51, 64, 36, 71, 72, 38, 28] (normal_endpoints 1147) h]
    exact Submodule.zero_mem _
lemma extension_1148_9 : a k 9*normalRep k 1148=normalRep k 1227 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1148 (b : Fin 75) : a k b*normalRep k 1148 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1148_9 k]
      exact normal_mem k 1227
  · rw [show a k b*normalRep k 1148=0 from arrow_incompatible k b 38 9 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1148) h]
    exact Submodule.zero_mem _
lemma extension_1149_52 : a k 52*normalRep k 1149=normalRep k 1227 := by
  change a k 52*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_913 (a k) (relation_zero k) (e k 38)
lemma extension_1149_53 : a k 53*normalRep k 1149=normalRep k 1228 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1149 (b : Fin 75) : a k b*normalRep k 1149 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1149_52 k]
      exact normal_mem k 1227
    · rw [extension_1149_53 k]
      exact normal_mem k 1228
  · rw [show a k b*normalRep k 1149=0 from arrow_incompatible k b 38 37 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1149) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
