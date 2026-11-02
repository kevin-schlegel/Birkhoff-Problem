import N6NormalData
import N6Reduced13
import N6Reduced14
import N6Reduced15
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_1050_4 : a k 4*normalRep k 1050=normalRep k 1137 := by
  change a k 4*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 25, 60]=walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_869 (a k) (relation_zero k) (e k 32)
lemma arrow_span_1050 (b : Fin 75) : a k b*normalRep k 1050 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1050_4 k]
      exact normal_mem k 1137
  · rw [show a k b*normalRep k 1050=0 from arrow_incompatible k b 32 4 [43, 47, 7, 17, 21, 69, 8, 66, 25, 60] (normal_endpoints 1050) h]
    exact Submodule.zero_mem _
lemma extension_1051_9 : a k 9*normalRep k 1051=normalRep k 1138 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1051 (b : Fin 75) : a k b*normalRep k 1051 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1051_9 k]
      exact normal_mem k 1138
  · rw [show a k b*normalRep k 1051=0 from arrow_incompatible k b 33 9 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18] (normal_endpoints 1051) h]
    exact Submodule.zero_mem _
lemma extension_1052_52 : a k 52*normalRep k 1052=normalRep k 1138 := by
  change a k 52*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19]=walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_831 (a k) (relation_zero k) (e k 33)
lemma extension_1052_53 : a k 53*normalRep k 1052=normalRep k 1139 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1052 (b : Fin 75) : a k b*normalRep k 1052 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1052_52 k]
      exact normal_mem k 1138
    · rw [extension_1052_53 k]
      exact normal_mem k 1139
  · rw [show a k b*normalRep k 1052=0 from arrow_incompatible k b 33 37 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19] (normal_endpoints 1052) h]
    exact Submodule.zero_mem _
lemma extension_1053_4 : a k 4*normalRep k 1053=normalRep k 1139 := by
  change a k 4*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 25, 60]=walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_870 (a k) (relation_zero k) (e k 33)
lemma arrow_span_1053 (b : Fin 75) : a k b*normalRep k 1053 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1053_4 k]
      exact normal_mem k 1139
  · rw [show a k b*normalRep k 1053=0 from arrow_incompatible k b 33 4 [45, 6, 7, 17, 21, 69, 8, 66, 25, 60] (normal_endpoints 1053) h]
    exact Submodule.zero_mem _
lemma extension_1054_41 : a k 41*normalRep k 1054=normalRep k 1140 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1054_42 : a k 42*normalRep k 1054=0 := by
  change a k 42*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_810 (a k) (relation_zero k) (e k 34)
lemma arrow_span_1054 (b : Fin 75) : a k b*normalRep k 1054 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1054_41 k]
      exact normal_mem k 1140
    · rw [extension_1054_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1054=0 from arrow_incompatible k b 34 31 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9] (normal_endpoints 1054) h]
    exact Submodule.zero_mem _
lemma extension_1055_54 : a k 54*normalRep k 1055=normalRep k 1141 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1055_55 : a k 55*normalRep k 1055=0 := by
  change a k 55*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_813 (a k) (relation_zero k) (e k 34)
lemma extension_1055_56 : a k 56*normalRep k 1055=normalRep k 1140 := by
  change a k 56*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 19, 53]=walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_857 (a k) (relation_zero k) (e k 34)
lemma arrow_span_1055 (b : Fin 75) : a k b*normalRep k 1055 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1055_54 k]
      exact normal_mem k 1141
    · rw [extension_1055_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1055_56 k]
      exact normal_mem k 1140
  · rw [show a k b*normalRep k 1055=0 from arrow_incompatible k b 34 38 [47, 7, 17, 21, 69, 8, 66, 24, 19, 53] (normal_endpoints 1055) h]
    exact Submodule.zero_mem _
lemma extension_1056_5 : a k 5*normalRep k 1056=normalRep k 1142 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1056 (b : Fin 75) : a k b*normalRep k 1056 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1056_5 k]
      exact normal_mem k 1142
  · rw [show a k b*normalRep k 1056=0 from arrow_incompatible k b 35 5 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1056) h]
    exact Submodule.zero_mem _
lemma extension_1057_33 : a k 33*normalRep k 1057=0 := by
  change a k 33*walk k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_804 (a k) (relation_zero k) (e k 35)
lemma extension_1057_34 : a k 34*normalRep k 1057=normalRep k 1142 := by
  change a k 34*walk k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_867 (a k) (relation_zero k) (e k 35)
lemma arrow_span_1057 (b : Fin 75) : a k b*normalRep k 1057 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1057_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1057_34 k]
      exact normal_mem k 1142
  · rw [show a k b*normalRep k 1057=0 from arrow_incompatible k b 35 26 [49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1057) h]
    exact Submodule.zero_mem _
lemma extension_1058_43 : a k 43*normalRep k 1058=0 := by
  change a k 43*walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_817 (a k) (relation_zero k) (e k 36)
lemma extension_1058_44 : a k 44*normalRep k 1058=normalRep k 1143 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1058 (b : Fin 75) : a k b*normalRep k 1058 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1058_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1058_44 k]
      exact normal_mem k 1143
  · rw [show a k b*normalRep k 1058=0 from arrow_incompatible k b 36 32 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1058) h]
    exact Submodule.zero_mem _
lemma extension_1059_15 : a k 15*normalRep k 1059=normalRep k 1144 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1059_16 : a k 16*normalRep k 1059=normalRep k 1143 := by
  change a k 16*walk k 36 [50, 17, 21, 69, 8, 66, 24, 19, 53, 54]=walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_863 (a k) (relation_zero k) (e k 36)
lemma arrow_span_1059 (b : Fin 75) : a k b*normalRep k 1059 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1059_15 k]
      exact normal_mem k 1144
    · rw [extension_1059_16 k]
      exact normal_mem k 1143
  · rw [show a k b*normalRep k 1059=0 from arrow_incompatible k b 36 15 [50, 17, 21, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1059) h]
    exact Submodule.zero_mem _
lemma extension_1060_24 : a k 24*normalRep k 1060=normalRep k 1145 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66] 24).symm
lemma extension_1060_25 : a k 25*normalRep k 1060=normalRep k 1146 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66] 25).symm
lemma arrow_span_1060 (b : Fin 75) : a k b*normalRep k 1060 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1060_24 k]
      exact normal_mem k 1145
    · rw [extension_1060_25 k]
      exact normal_mem k 1146
  · rw [show a k b*normalRep k 1060=0 from arrow_incompatible k b 37 20 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66] (normal_endpoints 1060) h]
    exact Submodule.zero_mem _
lemma extension_1061_39 : a k 39*normalRep k 1061=0 := by
  change a k 39*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_808 (a k) (relation_zero k) (e k 37)
lemma extension_1061_40 : a k 40*normalRep k 1061=(-normalRep k 1146) := by
  change a k 40*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 68]=(-walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_876 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1061 (b : Fin 75) : a k b*normalRep k 1061 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1061_39 k]
      exact Submodule.zero_mem _
    · rw [extension_1061_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1146)
  · rw [show a k b*normalRep k 1061=0 from arrow_incompatible k b 37 30 [52, 41, 43, 47, 7, 17, 21, 69, 8, 68] (normal_endpoints 1061) h]
    exact Submodule.zero_mem _
lemma extension_1062_28 : a k 28*normalRep k 1062=normalRep k 1147 := by
  exact (walk_snoc k 37 [52, 41, 43, 48, 51, 64, 36, 71, 72, 38] 28).symm
lemma extension_1062_29 : a k 29*normalRep k 1062=(-normalRep k 1145) := by
  change a k 29*walk k 37 [52, 41, 43, 48, 51, 64, 36, 71, 72, 38]=(-walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24])
  rw [← walk_snoc]
  exact Universal.mul_reduced_849 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1062 (b : Fin 75) : a k b*normalRep k 1062 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1062_28 k]
      exact normal_mem k 1147
    · rw [extension_1062_29 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1145)
  · rw [show a k b*normalRep k 1062=0 from arrow_incompatible k b 37 23 [52, 41, 43, 48, 51, 64, 36, 71, 72, 38] (normal_endpoints 1062) h]
    exact Submodule.zero_mem _
lemma arrow_span_1063 (b : Fin 75) : a k b*normalRep k 1063 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1063=0 from arrow_incompatible k b 37 46 [52, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1063) h]
    exact Submodule.zero_mem _
lemma extension_1064_18 : a k 18*normalRep k 1064=normalRep k 1148 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_1064_19 : a k 19*normalRep k 1064=normalRep k 1149 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_1064 (b : Fin 75) : a k b*normalRep k 1064 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1064_18 k]
      exact normal_mem k 1148
    · rw [extension_1064_19 k]
      exact normal_mem k 1149
  · rw [show a k b*normalRep k 1064=0 from arrow_incompatible k b 38 17 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 1064) h]
    exact Submodule.zero_mem _
lemma extension_1065_60 : a k 60*normalRep k 1065=normalRep k 1150 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_1065_61 : a k 61*normalRep k 1065=0 := by
  change a k 61*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_839 (a k) (relation_zero k) (e k 38)
lemma extension_1065_62 : a k 62*normalRep k 1065=normalRep k 1149 := by
  change a k 62*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_841 (a k) (relation_zero k) (e k 38)
lemma arrow_span_1065 (b : Fin 75) : a k b*normalRep k 1065 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1065_60 k]
      exact normal_mem k 1150
    · rw [extension_1065_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1065_62 k]
      exact normal_mem k 1149
  · rw [show a k b*normalRep k 1065=0 from arrow_incompatible k b 38 40 [55, 27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 1065) h]
    exact Submodule.zero_mem _
lemma extension_1066_14 : a k 14*normalRep k 1066=normalRep k 1148 := by
  change a k 14*walk k 38 [55, 27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_844 (a k) (relation_zero k) (e k 38)
lemma arrow_span_1066 (b : Fin 75) : a k b*normalRep k 1066 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1066_14 k]
      exact normal_mem k 1148
  · rw [show a k b*normalRep k 1066=0 from arrow_incompatible k b 38 14 [55, 27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 1066) h]
    exact Submodule.zero_mem _
lemma extension_1067_41 : a k 41*normalRep k 1067=normalRep k 1151 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1067_42 : a k 42*normalRep k 1067=0 := by
  change a k 42*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_811 (a k) (relation_zero k) (e k 39)
lemma arrow_span_1067 (b : Fin 75) : a k b*normalRep k 1067 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1067_41 k]
      exact normal_mem k 1151
    · rw [extension_1067_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1067=0 from arrow_incompatible k b 39 31 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1067) h]
    exact Submodule.zero_mem _
lemma extension_1068_54 : a k 54*normalRep k 1068=normalRep k 1152 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1068_55 : a k 55*normalRep k 1068=0 := by
  change a k 55*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_814 (a k) (relation_zero k) (e k 39)
lemma extension_1068_56 : a k 56*normalRep k 1068=normalRep k 1151 := by
  change a k 56*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_858 (a k) (relation_zero k) (e k 39)
lemma arrow_span_1068 (b : Fin 75) : a k b*normalRep k 1068 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1068_54 k]
      exact normal_mem k 1152
    · rw [extension_1068_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1068_56 k]
      exact normal_mem k 1151
  · rw [show a k b*normalRep k 1068=0 from arrow_incompatible k b 39 38 [58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1068) h]
    exact Submodule.zero_mem _
lemma extension_1069_0 : a k 0*normalRep k 1069=normalRep k 1153 := by
  exact (walk_snoc k 40 [60, 4, 54, 15, 1, 34, 63, 20, 30, 2] 0).symm
lemma arrow_span_1069 (b : Fin 75) : a k b*normalRep k 1069 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1069_0 k]
      exact normal_mem k 1153
  · rw [show a k b*normalRep k 1069=0 from arrow_incompatible k b 40 0 [60, 4, 54, 15, 1, 34, 63, 20, 30, 2] (normal_endpoints 1069) h]
    exact Submodule.zero_mem _
lemma extension_1070_66 : a k 66*normalRep k 1070=normalRep k 1154 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_1070_67 : a k 67*normalRep k 1070=0 := by
  change a k 67*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_821 (a k) (relation_zero k) (e k 40)
lemma extension_1070_68 : a k 68*normalRep k 1070=normalRep k 1155 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_1070 (b : Fin 75) : a k b*normalRep k 1070 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1070_66 k]
      exact normal_mem k 1154
    · rw [extension_1070_67 k]
      exact Submodule.zero_mem _
    · rw [extension_1070_68 k]
      exact normal_mem k 1155
  · rw [show a k b*normalRep k 1070=0 from arrow_incompatible k b 40 42 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8] (normal_endpoints 1070) h]
    exact Submodule.zero_mem _
lemma extension_1071_37 : a k 37*normalRep k 1071=normalRep k 1154 := by
  change a k 37*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 71, 72]=walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_882 (a k) (relation_zero k) (e k 40)
lemma extension_1071_38 : a k 38*normalRep k 1071=normalRep k 1156 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_1071 (b : Fin 75) : a k b*normalRep k 1071 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1071_37 k]
      exact normal_mem k 1154
    · rw [extension_1071_38 k]
      exact normal_mem k 1156
  · rw [show a k b*normalRep k 1071=0 from arrow_incompatible k b 40 29 [61, 35, 55, 27, 58, 33, 13, 49, 71, 72] (normal_endpoints 1071) h]
    exact Submodule.zero_mem _
lemma extension_1072_3 : a k 3*normalRep k 1072=(-normalRep k 1155) := by
  change a k 3*walk k 40 [61, 35, 55, 27, 58, 34, 63, 21, 70, 22]=(-walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_837 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1072 (b : Fin 75) : a k b*normalRep k 1072 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1072_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1155)
  · rw [show a k b*normalRep k 1072=0 from arrow_incompatible k b 40 3 [61, 35, 55, 27, 58, 34, 63, 21, 70, 22] (normal_endpoints 1072) h]
    exact Submodule.zero_mem _
lemma extension_1073_57 : a k 57*normalRep k 1073=normalRep k 1157 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1073_58 : a k 58*normalRep k 1073=normalRep k 1158 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1073_59 : a k 59*normalRep k 1073=0 := by
  change a k 59*walk k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_827 (a k) (relation_zero k) (e k 41)
lemma arrow_span_1073 (b : Fin 75) : a k b*normalRep k 1073 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1073_57 k]
      exact normal_mem k 1157
    · rw [extension_1073_58 k]
      exact normal_mem k 1158
    · rw [extension_1073_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1073=0 from arrow_incompatible k b 41 39 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1073) h]
    exact Submodule.zero_mem _
lemma extension_1074_1 : a k 1*normalRep k 1074=normalRep k 1158 := by
  change a k 1*walk k 41 [63, 21, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_824 (a k) (relation_zero k) (e k 41)
lemma arrow_span_1074 (b : Fin 75) : a k b*normalRep k 1074 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1074_1 k]
      exact normal_mem k 1158
  · rw [show a k b*normalRep k 1074=0 from arrow_incompatible k b 41 1 [63, 21, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1074) h]
    exact Submodule.zero_mem _
lemma extension_1075_30 : a k 30*normalRep k 1075=normalRep k 1159 := by
  exact (walk_snoc k 42 [66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1075_31 : a k 31*normalRep k 1075=0 := by
  change a k 31*walk k 42 [66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_834 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1075 (b : Fin 75) : a k b*normalRep k 1075 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1075_30 k]
      exact normal_mem k 1159
    · rw [extension_1075_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1075=0 from arrow_incompatible k b 42 24 [66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1075) h]
    exact Submodule.zero_mem _
lemma extension_1076_69 : a k 69*normalRep k 1076=normalRep k 1160 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 69).symm
lemma extension_1076_70 : a k 70*normalRep k 1076=0 := by
  change a k 70*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_854 (a k) (relation_zero k) (e k 42)
lemma extension_1076_71 : a k 71*normalRep k 1076=normalRep k 1161 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 71).symm
lemma arrow_span_1076 (b : Fin 75) : a k b*normalRep k 1076 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1076_69 k]
      exact normal_mem k 1160
    · rw [extension_1076_70 k]
      exact Submodule.zero_mem _
    · rw [extension_1076_71 k]
      exact normal_mem k 1161
  · rw [show a k b*normalRep k 1076=0 from arrow_incompatible k b 42 43 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49] (normal_endpoints 1076) h]
    exact Submodule.zero_mem _
lemma extension_1077_69 : a k 69*normalRep k 1077=(-normalRep k 1160) := by
  change a k 69*walk k 42 [67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=(-walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_847 (a k) (relation_zero k) (e k 42)
lemma extension_1077_70 : a k 70*normalRep k 1077=normalRep k 1162 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 34, 63, 21] 70).symm
lemma extension_1077_71 : a k 71*normalRep k 1077=0 := by
  change a k 71*walk k 42 [67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_835 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1077 (b : Fin 75) : a k b*normalRep k 1077 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1077_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1160)
    · rw [extension_1077_70 k]
      exact normal_mem k 1162
    · rw [extension_1077_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1077=0 from arrow_incompatible k b 42 43 [67, 32, 61, 35, 55, 27, 58, 34, 63, 21] (normal_endpoints 1077) h]
    exact Submodule.zero_mem _
lemma extension_1078_63 : a k 63*normalRep k 1078=normalRep k 1163 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1078_64 : a k 64*normalRep k 1078=0 := by
  change a k 64*walk k 43 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_805 (a k) (relation_zero k) (e k 43)
lemma extension_1078_65 : a k 65*normalRep k 1078=0 := by
  change a k 65*walk k 43 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_818 (a k) (relation_zero k) (e k 43)
lemma arrow_span_1078 (b : Fin 75) : a k b*normalRep k 1078 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1078_63 k]
      exact normal_mem k 1163
    · rw [extension_1078_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1078_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1078=0 from arrow_incompatible k b 43 41 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1078) h]
    exact Submodule.zero_mem _
lemma extension_1079_63 : a k 63*normalRep k 1079=normalRep k 1164 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34] 63).symm
lemma extension_1079_64 : a k 64*normalRep k 1079=0 := by
  change a k 64*walk k 43 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_806 (a k) (relation_zero k) (e k 43)
lemma extension_1079_65 : a k 65*normalRep k 1079=0 := by
  change a k 65*walk k 43 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_819 (a k) (relation_zero k) (e k 43)
lemma arrow_span_1079 (b : Fin 75) : a k b*normalRep k 1079 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1079_63 k]
      exact normal_mem k 1164
    · rw [extension_1079_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1079_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1079=0 from arrow_incompatible k b 43 41 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34] (normal_endpoints 1079) h]
    exact Submodule.zero_mem _
lemma extension_1080_20 : a k 20*normalRep k 1080=normalRep k 1165 := by
  exact (walk_snoc k 44 [72, 37, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1080_21 : a k 21*normalRep k 1080=0 := by
  change a k 21*walk k 44 [72, 37, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_873 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1080 (b : Fin 75) : a k b*normalRep k 1080 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1080_20 k]
      exact normal_mem k 1165
    · rw [extension_1080_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1080=0 from arrow_incompatible k b 44 18 [72, 37, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1080) h]
    exact Submodule.zero_mem _
lemma extension_1081_49 : a k 49*normalRep k 1081=normalRep k 1166 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13] 49).symm
lemma arrow_span_1081 (b : Fin 75) : a k b*normalRep k 1081 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1081_49 k]
      exact normal_mem k 1166
  · rw [show a k b*normalRep k 1081=0 from arrow_incompatible k b 44 35 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13] (normal_endpoints 1081) h]
    exact Submodule.zero_mem _
lemma extension_1082_20 : a k 20*normalRep k 1082=0 := by
  change a k 20*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_828 (a k) (relation_zero k) (e k 44)
lemma extension_1082_21 : a k 21*normalRep k 1082=normalRep k 1167 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63] 21).symm
lemma arrow_span_1082 (b : Fin 75) : a k b*normalRep k 1082 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1082_20 k]
      exact Submodule.zero_mem _
    · rw [extension_1082_21 k]
      exact normal_mem k 1167
  · rw [show a k b*normalRep k 1082=0 from arrow_incompatible k b 44 18 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63] (normal_endpoints 1082) h]
    exact Submodule.zero_mem _
lemma extension_1083_36 : a k 36*normalRep k 1083=normalRep k 1167 + normalRep k 1166 := by
  change a k 36*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34, 64]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_874 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1083 (b : Fin 75) : a k b*normalRep k 1083 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1083_36 k]
      exact (normalSpan k).add_mem (normal_mem k 1167) (normal_mem k 1166)
  · rw [show a k b*normalRep k 1083=0 from arrow_incompatible k b 44 28 [73, 67, 32, 61, 35, 55, 27, 58, 34, 64] (normal_endpoints 1083) h]
    exact Submodule.zero_mem _
lemma extension_1084_54 : a k 54*normalRep k 1084=0 := by
  change a k 54*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_846 (a k) (relation_zero k) (e k 45)
lemma extension_1084_55 : a k 55*normalRep k 1084=normalRep k 1168 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35] 55).symm
lemma extension_1084_56 : a k 56*normalRep k 1084=normalRep k 1169 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35] 56).symm
lemma arrow_span_1084 (b : Fin 75) : a k b*normalRep k 1084 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1084_54 k]
      exact Submodule.zero_mem _
    · rw [extension_1084_55 k]
      exact normal_mem k 1168
    · rw [extension_1084_56 k]
      exact normal_mem k 1169
  · rw [show a k b*normalRep k 1084=0 from arrow_incompatible k b 45 38 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35] (normal_endpoints 1084) h]
    exact Submodule.zero_mem _
lemma extension_1085_41 : a k 41*normalRep k 1085=normalRep k 1169 := by
  change a k 41*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 62, 52]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_859 (a k) (relation_zero k) (e k 45)
lemma extension_1085_42 : a k 42*normalRep k 1085=normalRep k 1170 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 62, 52] 42).symm
lemma arrow_span_1085 (b : Fin 75) : a k b*normalRep k 1085 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1085_41 k]
      exact normal_mem k 1169
    · rw [extension_1085_42 k]
      exact normal_mem k 1170
  · rw [show a k b*normalRep k 1085=0 from arrow_incompatible k b 45 31 [74, 10, 11, 26, 31, 73, 67, 32, 62, 52] (normal_endpoints 1085) h]
    exact Submodule.zero_mem _
lemma extension_1086_2 : a k 2*normalRep k 1086=normalRep k 1171 := by
  exact (walk_snoc k 3 [3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30] 2).symm
lemma arrow_span_1086 (b : Fin 75) : a k b*normalRep k 1086 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1086_2 k]
      exact normal_mem k 1171
  · rw [show a k b*normalRep k 1086=0 from arrow_incompatible k b 3 2 [3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30] (normal_endpoints 1086) h]
    exact Submodule.zero_mem _
lemma extension_1087_43 : a k 43*normalRep k 1087=0 := by
  change a k 43*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_897 (a k) (relation_zero k) (e k 6)
lemma extension_1087_44 : a k 44*normalRep k 1087=normalRep k 1172 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1087 (b : Fin 75) : a k b*normalRep k 1087 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1087_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1087_44 k]
      exact normal_mem k 1172
  · rw [show a k b*normalRep k 1087=0 from arrow_incompatible k b 6 32 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1087) h]
    exact Submodule.zero_mem _
lemma extension_1088_15 : a k 15*normalRep k 1088=normalRep k 1173 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1088_16 : a k 16*normalRep k 1088=normalRep k 1172 := by
  change a k 16*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]=walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_940 (a k) (relation_zero k) (e k 6)
lemma arrow_span_1088 (b : Fin 75) : a k b*normalRep k 1088 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1088_15 k]
      exact normal_mem k 1173
    · rw [extension_1088_16 k]
      exact normal_mem k 1172
  · rw [show a k b*normalRep k 1088=0 from arrow_incompatible k b 6 15 [6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1088) h]
    exact Submodule.zero_mem _
lemma extension_1089_57 : a k 57*normalRep k 1089=normalRep k 1174 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1089_58 : a k 58*normalRep k 1089=normalRep k 1175 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1089_59 : a k 59*normalRep k 1089=0 := by
  change a k 59*walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_908 (a k) (relation_zero k) (e k 7)
lemma arrow_span_1089 (b : Fin 75) : a k b*normalRep k 1089 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1089_57 k]
      exact normal_mem k 1174
    · rw [extension_1089_58 k]
      exact normal_mem k 1175
    · rw [extension_1089_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1089=0 from arrow_incompatible k b 7 39 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1089) h]
    exact Submodule.zero_mem _
lemma extension_1090_1 : a k 1*normalRep k 1090=normalRep k 1175 := by
  change a k 1*walk k 7 [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_905 (a k) (relation_zero k) (e k 7)
lemma arrow_span_1090 (b : Fin 75) : a k b*normalRep k 1090 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1090_1 k]
      exact normal_mem k 1175
  · rw [show a k b*normalRep k 1090=0 from arrow_incompatible k b 7 1 [7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1090) h]
    exact Submodule.zero_mem _
lemma extension_1091_30 : a k 30*normalRep k 1091=normalRep k 1176 := by
  exact (walk_snoc k 8 [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1091_31 : a k 31*normalRep k 1091=0 := by
  change a k 31*walk k 8 [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_914 (a k) (relation_zero k) (e k 8)
lemma arrow_span_1091 (b : Fin 75) : a k b*normalRep k 1091 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1091_30 k]
      exact normal_mem k 1176
    · rw [extension_1091_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1091=0 from arrow_incompatible k b 8 24 [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1091) h]
    exact Submodule.zero_mem _
lemma extension_1092_57 : a k 57*normalRep k 1092=0 := by
  change a k 57*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_924 (a k) (relation_zero k) (e k 10)
lemma extension_1092_58 : a k 58*normalRep k 1092=normalRep k 1177 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27] 58).symm
lemma extension_1092_59 : a k 59*normalRep k 1092=normalRep k 1178 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27] 59).symm
lemma arrow_span_1092 (b : Fin 75) : a k b*normalRep k 1092 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1092_57 k]
      exact Submodule.zero_mem _
    · rw [extension_1092_58 k]
      exact normal_mem k 1177
    · rw [extension_1092_59 k]
      exact normal_mem k 1178
  · rw [show a k b*normalRep k 1092=0 from arrow_incompatible k b 10 39 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27] (normal_endpoints 1092) h]
    exact Submodule.zero_mem _
lemma extension_1093_47 : a k 47*normalRep k 1093=normalRep k 1179 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43] 47).symm
lemma extension_1093_48 : a k 48*normalRep k 1093=normalRep k 1178 := by
  change a k 48*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59]
  rw [← walk_snoc]
  exact Universal.mul_reduced_932 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1093 (b : Fin 75) : a k b*normalRep k 1093 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1093_47 k]
      exact normal_mem k 1179
    · rw [extension_1093_48 k]
      exact normal_mem k 1178
  · rw [show a k b*normalRep k 1093=0 from arrow_incompatible k b 10 34 [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43] (normal_endpoints 1093) h]
    exact Submodule.zero_mem _
lemma extension_1094_6 : a k 6*normalRep k 1094=normalRep k 1179 := by
  change a k 6*walk k 10 [10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47]
  rw [← walk_snoc]
  exact Universal.mul_reduced_933 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1094 (b : Fin 75) : a k b*normalRep k 1094 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1094_6 k]
      exact normal_mem k 1179
  · rw [show a k b*normalRep k 1094=0 from arrow_incompatible k b 10 6 [10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45] (normal_endpoints 1094) h]
    exact Submodule.zero_mem _
lemma extension_1095_33 : a k 33*normalRep k 1095=normalRep k 1180 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58] 33).symm
lemma extension_1095_34 : a k 34*normalRep k 1095=normalRep k 1181 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58] 34).symm
lemma arrow_span_1095 (b : Fin 75) : a k b*normalRep k 1095 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1095_33 k]
      exact normal_mem k 1180
    · rw [extension_1095_34 k]
      exact normal_mem k 1181
  · rw [show a k b*normalRep k 1095=0 from arrow_incompatible k b 11 26 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58] (normal_endpoints 1095) h]
    exact Submodule.zero_mem _
lemma extension_1096_50 : a k 50*normalRep k 1096=normalRep k 1182 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59] 50).symm
lemma extension_1096_51 : a k 51*normalRep k 1096=normalRep k 1181 := by
  change a k 51*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_944 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1096 (b : Fin 75) : a k b*normalRep k 1096 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1096_50 k]
      exact normal_mem k 1182
    · rw [extension_1096_51 k]
      exact normal_mem k 1181
  · rw [show a k b*normalRep k 1096=0 from arrow_incompatible k b 11 36 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59] (normal_endpoints 1096) h]
    exact Submodule.zero_mem _
lemma extension_1097_7 : a k 7*normalRep k 1097=normalRep k 1182 := by
  change a k 7*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]
  rw [← walk_snoc]
  exact Universal.mul_reduced_934 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1097 (b : Fin 75) : a k b*normalRep k 1097 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1097_7 k]
      exact normal_mem k 1182
  · rw [show a k b*normalRep k 1097=0 from arrow_incompatible k b 11 7 [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47] (normal_endpoints 1097) h]
    exact Submodule.zero_mem _
lemma extension_1098_24 : a k 24*normalRep k 1098=normalRep k 1183 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_1098_25 : a k 25*normalRep k 1098=normalRep k 1184 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_1098 (b : Fin 75) : a k b*normalRep k 1098 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1098_24 k]
      exact normal_mem k 1183
    · rw [extension_1098_25 k]
      exact normal_mem k 1184
  · rw [show a k b*normalRep k 1098=0 from arrow_incompatible k b 12 20 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 1098) h]
    exact Submodule.zero_mem _
lemma extension_1099_39 : a k 39*normalRep k 1099=0 := by
  change a k 39*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_889 (a k) (relation_zero k) (e k 12)
lemma extension_1099_40 : a k 40*normalRep k 1099=(-normalRep k 1184) := by
  change a k 40*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_953 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1099 (b : Fin 75) : a k b*normalRep k 1099 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1099_39 k]
      exact Submodule.zero_mem _
    · rw [extension_1099_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1184)
  · rw [show a k b*normalRep k 1099=0 from arrow_incompatible k b 12 30 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 1099) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
