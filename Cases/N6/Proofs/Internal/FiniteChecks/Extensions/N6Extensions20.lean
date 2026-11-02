import N6NormalData
import N6Reduced13
import N6Reduced14
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma arrow_span_1000 (b : Fin 75) : a k b*normalRep k 1000 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1000=0 from arrow_incompatible k b 9 46 [9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1000) h]
    exact Submodule.zero_mem _
lemma extension_1001_27 : a k 27*normalRep k 1001=normalRep k 1092 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55] 27).symm
lemma arrow_span_1001 (b : Fin 75) : a k b*normalRep k 1001 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1001_27 k]
      exact normal_mem k 1092
  · rw [show a k b*normalRep k 1001=0 from arrow_incompatible k b 10 22 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55] (normal_endpoints 1001) h]
    exact Submodule.zero_mem _
lemma extension_1002_43 : a k 43*normalRep k 1002=normalRep k 1093 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 56] 43).symm
lemma extension_1002_44 : a k 44*normalRep k 1002=normalRep k 1092 := by
  change a k 44*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 56]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27]
  rw [← walk_snoc]
  exact Universal.mul_reduced_861 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1002 (b : Fin 75) : a k b*normalRep k 1002 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1002_43 k]
      exact normal_mem k 1093
    · rw [extension_1002_44 k]
      exact normal_mem k 1092
  · rw [show a k b*normalRep k 1002=0 from arrow_incompatible k b 10 32 [10, 11, 26, 31, 73, 67, 32, 61, 35, 56] (normal_endpoints 1002) h]
    exact Submodule.zero_mem _
lemma extension_1003_45 : a k 45*normalRep k 1003=normalRep k 1094 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 62, 52, 42] 45).symm
lemma extension_1003_46 : a k 46*normalRep k 1003=normalRep k 1093 := by
  change a k 46*walk k 10 [10, 11, 26, 31, 73, 67, 32, 62, 52, 42]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43]
  rw [← walk_snoc]
  exact Universal.mul_reduced_850 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1003 (b : Fin 75) : a k b*normalRep k 1003 ∈ normalSpan k := by
  by_cases h : arrowSource b=33
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [45, 46] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1003_45 k]
      exact normal_mem k 1094
    · rw [extension_1003_46 k]
      exact normal_mem k 1093
  · rw [show a k b*normalRep k 1003=0 from arrow_incompatible k b 10 33 [10, 11, 26, 31, 73, 67, 32, 62, 52, 42] (normal_endpoints 1003) h]
    exact Submodule.zero_mem _
lemma extension_1004_57 : a k 57*normalRep k 1004=0 := by
  change a k 57*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_842 (a k) (relation_zero k) (e k 11)
lemma extension_1004_58 : a k 58*normalRep k 1004=normalRep k 1095 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27] 58).symm
lemma extension_1004_59 : a k 59*normalRep k 1004=normalRep k 1096 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27] 59).symm
lemma arrow_span_1004 (b : Fin 75) : a k b*normalRep k 1004 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1004_57 k]
      exact Submodule.zero_mem _
    · rw [extension_1004_58 k]
      exact normal_mem k 1095
    · rw [extension_1004_59 k]
      exact normal_mem k 1096
  · rw [show a k b*normalRep k 1004=0 from arrow_incompatible k b 11 39 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27] (normal_endpoints 1004) h]
    exact Submodule.zero_mem _
lemma extension_1005_47 : a k 47*normalRep k 1005=normalRep k 1097 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 56, 43] 47).symm
lemma extension_1005_48 : a k 48*normalRep k 1005=normalRep k 1096 := by
  change a k 48*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 56, 43]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59]
  rw [← walk_snoc]
  exact Universal.mul_reduced_851 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1005 (b : Fin 75) : a k b*normalRep k 1005 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1005_47 k]
      exact normal_mem k 1097
    · rw [extension_1005_48 k]
      exact normal_mem k 1096
  · rw [show a k b*normalRep k 1005=0 from arrow_incompatible k b 11 34 [11, 26, 31, 73, 67, 32, 61, 35, 56, 43] (normal_endpoints 1005) h]
    exact Submodule.zero_mem _
lemma extension_1006_6 : a k 6*normalRep k 1006=normalRep k 1097 := by
  change a k 6*walk k 11 [11, 26, 31, 73, 67, 32, 62, 52, 42, 45]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47]
  rw [← walk_snoc]
  exact Universal.mul_reduced_852 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1006 (b : Fin 75) : a k b*normalRep k 1006 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1006_6 k]
      exact normal_mem k 1097
  · rw [show a k b*normalRep k 1006=0 from arrow_incompatible k b 11 6 [11, 26, 31, 73, 67, 32, 62, 52, 42, 45] (normal_endpoints 1006) h]
    exact Submodule.zero_mem _
lemma extension_1007_66 : a k 66*normalRep k 1007=normalRep k 1098 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_1007_67 : a k 67*normalRep k 1007=0 := by
  change a k 67*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_820 (a k) (relation_zero k) (e k 12)
lemma extension_1007_68 : a k 68*normalRep k 1007=normalRep k 1099 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_1007 (b : Fin 75) : a k b*normalRep k 1007 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1007_66 k]
      exact normal_mem k 1098
    · rw [extension_1007_67 k]
      exact Submodule.zero_mem _
    · rw [extension_1007_68 k]
      exact normal_mem k 1099
  · rw [show a k b*normalRep k 1007=0 from arrow_incompatible k b 12 42 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8] (normal_endpoints 1007) h]
    exact Submodule.zero_mem _
lemma extension_1008_37 : a k 37*normalRep k 1008=normalRep k 1098 := by
  change a k 37*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 71, 72]=walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_881 (a k) (relation_zero k) (e k 12)
lemma extension_1008_38 : a k 38*normalRep k 1008=normalRep k 1100 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_1008 (b : Fin 75) : a k b*normalRep k 1008 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1008_37 k]
      exact normal_mem k 1098
    · rw [extension_1008_38 k]
      exact normal_mem k 1100
  · rw [show a k b*normalRep k 1008=0 from arrow_incompatible k b 12 29 [12, 35, 55, 27, 58, 33, 13, 49, 71, 72] (normal_endpoints 1008) h]
    exact Submodule.zero_mem _
lemma extension_1009_3 : a k 3*normalRep k 1009=(-normalRep k 1099) := by
  change a k 3*walk k 12 [12, 35, 55, 27, 58, 34, 63, 21, 70, 22]=(-walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_836 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1009 (b : Fin 75) : a k b*normalRep k 1009 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1009_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1099)
  · rw [show a k b*normalRep k 1009=0 from arrow_incompatible k b 12 3 [12, 35, 55, 27, 58, 34, 63, 21, 70, 22] (normal_endpoints 1009) h]
    exact Submodule.zero_mem _
lemma extension_1010_57 : a k 57*normalRep k 1010=normalRep k 1101 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1010_58 : a k 58*normalRep k 1010=normalRep k 1102 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1010_59 : a k 59*normalRep k 1010=0 := by
  change a k 59*walk k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_825 (a k) (relation_zero k) (e k 13)
lemma arrow_span_1010 (b : Fin 75) : a k b*normalRep k 1010 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1010_57 k]
      exact normal_mem k 1101
    · rw [extension_1010_58 k]
      exact normal_mem k 1102
    · rw [extension_1010_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1010=0 from arrow_incompatible k b 13 39 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1010) h]
    exact Submodule.zero_mem _
lemma extension_1011_1 : a k 1*normalRep k 1011=normalRep k 1102 := by
  change a k 1*walk k 13 [13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_822 (a k) (relation_zero k) (e k 13)
lemma arrow_span_1011 (b : Fin 75) : a k b*normalRep k 1011 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1011_1 k]
      exact normal_mem k 1102
  · rw [show a k b*normalRep k 1011=0 from arrow_incompatible k b 13 1 [13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1011) h]
    exact Submodule.zero_mem _
lemma extension_1012_0 : a k 0*normalRep k 1012=normalRep k 1103 := by
  exact (walk_snoc k 14 [14, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1012 (b : Fin 75) : a k b*normalRep k 1012 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1012_0 k]
      exact normal_mem k 1103
  · rw [show a k b*normalRep k 1012=0 from arrow_incompatible k b 14 0 [14, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1012) h]
    exact Submodule.zero_mem _
lemma extension_1013_57 : a k 57*normalRep k 1013=normalRep k 1104 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1013_58 : a k 58*normalRep k 1013=normalRep k 1105 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1013_59 : a k 59*normalRep k 1013=0 := by
  change a k 59*walk k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_826 (a k) (relation_zero k) (e k 16)
lemma arrow_span_1013 (b : Fin 75) : a k b*normalRep k 1013 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1013_57 k]
      exact normal_mem k 1104
    · rw [extension_1013_58 k]
      exact normal_mem k 1105
    · rw [extension_1013_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1013=0 from arrow_incompatible k b 16 39 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1013) h]
    exact Submodule.zero_mem _
lemma extension_1014_1 : a k 1*normalRep k 1014=normalRep k 1105 := by
  change a k 1*walk k 16 [17, 21, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_823 (a k) (relation_zero k) (e k 16)
lemma arrow_span_1014 (b : Fin 75) : a k b*normalRep k 1014 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1014_1 k]
      exact normal_mem k 1105
  · rw [show a k b*normalRep k 1014=0 from arrow_incompatible k b 16 1 [17, 21, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1014) h]
    exact Submodule.zero_mem _
lemma extension_1015_0 : a k 0*normalRep k 1015=normalRep k 1106 := by
  exact (walk_snoc k 17 [18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1015 (b : Fin 75) : a k b*normalRep k 1015 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1015_0 k]
      exact normal_mem k 1106
  · rw [show a k b*normalRep k 1015=0 from arrow_incompatible k b 17 0 [18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1015) h]
    exact Submodule.zero_mem _
lemma extension_1016_5 : a k 5*normalRep k 1016=normalRep k 1107 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1016 (b : Fin 75) : a k b*normalRep k 1016 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1016_5 k]
      exact normal_mem k 1107
  · rw [show a k b*normalRep k 1016=0 from arrow_incompatible k b 18 5 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1016) h]
    exact Submodule.zero_mem _
lemma extension_1017_33 : a k 33*normalRep k 1017=0 := by
  change a k 33*walk k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_802 (a k) (relation_zero k) (e k 18)
lemma extension_1017_34 : a k 34*normalRep k 1017=normalRep k 1107 := by
  change a k 34*walk k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_864 (a k) (relation_zero k) (e k 18)
lemma arrow_span_1017 (b : Fin 75) : a k b*normalRep k 1017 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1017_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1017_34 k]
      exact normal_mem k 1107
  · rw [show a k b*normalRep k 1017=0 from arrow_incompatible k b 18 26 [21, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1017) h]
    exact Submodule.zero_mem _
lemma extension_1018_20 : a k 20*normalRep k 1018=normalRep k 1108 := by
  exact (walk_snoc k 19 [22, 3, 40, 60, 4, 54, 15, 1, 34, 63] 20).symm
lemma extension_1018_21 : a k 21*normalRep k 1018=0 := by
  change a k 21*walk k 19 [22, 3, 40, 60, 4, 54, 15, 1, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_872 (a k) (relation_zero k) (e k 19)
lemma arrow_span_1018 (b : Fin 75) : a k b*normalRep k 1018 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1018_20 k]
      exact normal_mem k 1108
    · rw [extension_1018_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1018=0 from arrow_incompatible k b 19 18 [22, 3, 40, 60, 4, 54, 15, 1, 34, 63] (normal_endpoints 1018) h]
    exact Submodule.zero_mem _
lemma extension_1019_2 : a k 2*normalRep k 1019=normalRep k 1109 := by
  exact (walk_snoc k 20 [24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1019 (b : Fin 75) : a k b*normalRep k 1019 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1019_2 k]
      exact normal_mem k 1109
  · rw [show a k b*normalRep k 1019=0 from arrow_incompatible k b 20 2 [24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1019) h]
    exact Submodule.zero_mem _
lemma extension_1020_33 : a k 33*normalRep k 1020=normalRep k 1110 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58] 33).symm
lemma extension_1020_34 : a k 34*normalRep k 1020=normalRep k 1111 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58] 34).symm
lemma arrow_span_1020 (b : Fin 75) : a k b*normalRep k 1020 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1020_33 k]
      exact normal_mem k 1110
    · rw [extension_1020_34 k]
      exact normal_mem k 1111
  · rw [show a k b*normalRep k 1020=0 from arrow_incompatible k b 21 26 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58] (normal_endpoints 1020) h]
    exact Submodule.zero_mem _
lemma extension_1021_50 : a k 50*normalRep k 1021=normalRep k 1112 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 59] 50).symm
lemma extension_1021_51 : a k 51*normalRep k 1021=normalRep k 1111 := by
  change a k 51*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 59]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_865 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1021 (b : Fin 75) : a k b*normalRep k 1021 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1021_50 k]
      exact normal_mem k 1112
    · rw [extension_1021_51 k]
      exact normal_mem k 1111
  · rw [show a k b*normalRep k 1021=0 from arrow_incompatible k b 21 36 [26, 31, 73, 67, 32, 61, 35, 55, 27, 59] (normal_endpoints 1021) h]
    exact Submodule.zero_mem _
lemma extension_1022_7 : a k 7*normalRep k 1022=normalRep k 1112 := by
  change a k 7*walk k 21 [26, 31, 73, 67, 32, 61, 35, 56, 43, 47]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]
  rw [← walk_snoc]
  exact Universal.mul_reduced_853 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1022 (b : Fin 75) : a k b*normalRep k 1022 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1022_7 k]
      exact normal_mem k 1112
  · rw [show a k b*normalRep k 1022=0 from arrow_incompatible k b 21 7 [26, 31, 73, 67, 32, 61, 35, 56, 43, 47] (normal_endpoints 1022) h]
    exact Submodule.zero_mem _
lemma extension_1023_9 : a k 9*normalRep k 1023=normalRep k 1113 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1023 (b : Fin 75) : a k b*normalRep k 1023 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1023_9 k]
      exact normal_mem k 1113
  · rw [show a k b*normalRep k 1023=0 from arrow_incompatible k b 22 9 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1023) h]
    exact Submodule.zero_mem _
lemma extension_1024_52 : a k 52*normalRep k 1024=normalRep k 1113 := by
  change a k 52*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_829 (a k) (relation_zero k) (e k 22)
lemma extension_1024_53 : a k 53*normalRep k 1024=normalRep k 1114 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1024 (b : Fin 75) : a k b*normalRep k 1024 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1024_52 k]
      exact normal_mem k 1113
    · rw [extension_1024_53 k]
      exact normal_mem k 1114
  · rw [show a k b*normalRep k 1024=0 from arrow_incompatible k b 22 37 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1024) h]
    exact Submodule.zero_mem _
lemma extension_1025_4 : a k 4*normalRep k 1025=normalRep k 1114 := by
  change a k 4*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_868 (a k) (relation_zero k) (e k 22)
lemma arrow_span_1025 (b : Fin 75) : a k b*normalRep k 1025 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1025_4 k]
      exact normal_mem k 1114
  · rw [show a k b*normalRep k 1025=0 from arrow_incompatible k b 22 4 [27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1025) h]
    exact Submodule.zero_mem _
lemma extension_1026_2 : a k 2*normalRep k 1026=normalRep k 1115 := by
  exact (walk_snoc k 23 [28, 14, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1026 (b : Fin 75) : a k b*normalRep k 1026 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1026_2 k]
      exact normal_mem k 1115
  · rw [show a k b*normalRep k 1026=0 from arrow_incompatible k b 23 2 [28, 14, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1026) h]
    exact Submodule.zero_mem _
lemma extension_1027_13 : a k 13*normalRep k 1027=normalRep k 1116 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33] 13).symm
lemma arrow_span_1027 (b : Fin 75) : a k b*normalRep k 1027 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1027_13 k]
      exact normal_mem k 1116
  · rw [show a k b*normalRep k 1027=0 from arrow_incompatible k b 24 13 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33] (normal_endpoints 1027) h]
    exact Submodule.zero_mem _
lemma extension_1028_63 : a k 63*normalRep k 1028=normalRep k 1117 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34] 63).symm
lemma extension_1028_64 : a k 64*normalRep k 1028=normalRep k 1118 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34] 64).symm
lemma extension_1028_65 : a k 65*normalRep k 1028=normalRep k 1116 := by
  change a k 65*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_845 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1028 (b : Fin 75) : a k b*normalRep k 1028 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1028_63 k]
      exact normal_mem k 1117
    · rw [extension_1028_64 k]
      exact normal_mem k 1118
    · rw [extension_1028_65 k]
      exact normal_mem k 1116
  · rw [show a k b*normalRep k 1028=0 from arrow_incompatible k b 24 41 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34] (normal_endpoints 1028) h]
    exact Submodule.zero_mem _
lemma extension_1029_17 : a k 17*normalRep k 1029=normalRep k 1117 := by
  change a k 17*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 59, 50]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_855 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1029 (b : Fin 75) : a k b*normalRep k 1029 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1029_17 k]
      exact normal_mem k 1117
  · rw [show a k b*normalRep k 1029=0 from arrow_incompatible k b 24 16 [31, 73, 67, 32, 61, 35, 55, 27, 59, 50] (normal_endpoints 1029) h]
    exact Submodule.zero_mem _
lemma extension_1030_8 : a k 8*normalRep k 1030=normalRep k 1119 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_1030 (b : Fin 75) : a k b*normalRep k 1030 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1030_8 k]
      exact normal_mem k 1119
  · rw [show a k b*normalRep k 1030=0 from arrow_incompatible k b 25 8 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69] (normal_endpoints 1030) h]
    exact Submodule.zero_mem _
lemma extension_1031_72 : a k 72*normalRep k 1031=normalRep k 1120 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 71] 72).symm
lemma extension_1031_73 : a k 73*normalRep k 1031=normalRep k 1119 := by
  change a k 73*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 71]=walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_877 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1031 (b : Fin 75) : a k b*normalRep k 1031 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1031_72 k]
      exact normal_mem k 1120
    · rw [extension_1031_73 k]
      exact normal_mem k 1119
  · rw [show a k b*normalRep k 1031=0 from arrow_incompatible k b 25 44 [32, 61, 35, 55, 27, 58, 33, 13, 49, 71] (normal_endpoints 1031) h]
    exact Submodule.zero_mem _
lemma extension_1032_22 : a k 22*normalRep k 1032=normalRep k 1121 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 34, 63, 21, 70] 22).symm
lemma extension_1032_23 : a k 23*normalRep k 1032=normalRep k 1119 := by
  change a k 23*walk k 25 [32, 61, 35, 55, 27, 58, 34, 63, 21, 70]=walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_878 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1032 (b : Fin 75) : a k b*normalRep k 1032 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1032_22 k]
      exact normal_mem k 1121
    · rw [extension_1032_23 k]
      exact normal_mem k 1119
  · rw [show a k b*normalRep k 1032=0 from arrow_incompatible k b 25 19 [32, 61, 35, 55, 27, 58, 34, 63, 21, 70] (normal_endpoints 1032) h]
    exact Submodule.zero_mem _
lemma extension_1033_43 : a k 43*normalRep k 1033=0 := by
  change a k 43*walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_816 (a k) (relation_zero k) (e k 26)
lemma extension_1033_44 : a k 44*normalRep k 1033=normalRep k 1122 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1033 (b : Fin 75) : a k b*normalRep k 1033 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1033_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1033_44 k]
      exact normal_mem k 1122
  · rw [show a k b*normalRep k 1033=0 from arrow_incompatible k b 26 32 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1033) h]
    exact Submodule.zero_mem _
lemma extension_1034_15 : a k 15*normalRep k 1034=normalRep k 1123 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1034_16 : a k 16*normalRep k 1034=normalRep k 1122 := by
  change a k 16*walk k 26 [33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_862 (a k) (relation_zero k) (e k 26)
lemma arrow_span_1034 (b : Fin 75) : a k b*normalRep k 1034 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1034_15 k]
      exact normal_mem k 1123
    · rw [extension_1034_16 k]
      exact normal_mem k 1122
  · rw [show a k b*normalRep k 1034=0 from arrow_incompatible k b 26 15 [33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1034) h]
    exact Submodule.zero_mem _
lemma extension_1035_24 : a k 24*normalRep k 1035=normalRep k 1124 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_1035_25 : a k 25*normalRep k 1035=normalRep k 1125 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_1035 (b : Fin 75) : a k b*normalRep k 1035 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1035_24 k]
      exact normal_mem k 1124
    · rw [extension_1035_25 k]
      exact normal_mem k 1125
  · rw [show a k b*normalRep k 1035=0 from arrow_incompatible k b 27 20 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 1035) h]
    exact Submodule.zero_mem _
lemma extension_1036_39 : a k 39*normalRep k 1036=0 := by
  change a k 39*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_807 (a k) (relation_zero k) (e k 27)
lemma extension_1036_40 : a k 40*normalRep k 1036=(-normalRep k 1125) := by
  change a k 40*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_875 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1036 (b : Fin 75) : a k b*normalRep k 1036 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1036_39 k]
      exact Submodule.zero_mem _
    · rw [extension_1036_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1125)
  · rw [show a k b*normalRep k 1036=0 from arrow_incompatible k b 27 30 [35, 55, 27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 1036) h]
    exact Submodule.zero_mem _
lemma extension_1037_28 : a k 28*normalRep k 1037=normalRep k 1126 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_1037_29 : a k 29*normalRep k 1037=normalRep k 1124 := by
  change a k 29*walk k 27 [35, 55, 27, 58, 33, 13, 49, 71, 72, 38]=walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_848 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1037 (b : Fin 75) : a k b*normalRep k 1037 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1037_28 k]
      exact normal_mem k 1126
    · rw [extension_1037_29 k]
      exact normal_mem k 1124
  · rw [show a k b*normalRep k 1037=0 from arrow_incompatible k b 27 23 [35, 55, 27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 1037) h]
    exact Submodule.zero_mem _
lemma extension_1038_33 : a k 33*normalRep k 1038=0 := by
  change a k 33*walk k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_803 (a k) (relation_zero k) (e k 28)
lemma extension_1038_34 : a k 34*normalRep k 1038=normalRep k 1127 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1] 34).symm
lemma arrow_span_1038 (b : Fin 75) : a k b*normalRep k 1038 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1038_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1038_34 k]
      exact normal_mem k 1127
  · rw [show a k b*normalRep k 1038=0 from arrow_incompatible k b 28 26 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1] (normal_endpoints 1038) h]
    exact Submodule.zero_mem _
lemma extension_1039_5 : a k 5*normalRep k 1039=normalRep k 1127 := by
  change a k 5*walk k 28 [36, 70, 22, 3, 40, 60, 4, 54, 16, 57]=walk k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_866 (a k) (relation_zero k) (e k 28)
lemma arrow_span_1039 (b : Fin 75) : a k b*normalRep k 1039 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1039_5 k]
      exact normal_mem k 1127
  · rw [show a k b*normalRep k 1039=0 from arrow_incompatible k b 28 5 [36, 70, 22, 3, 40, 60, 4, 54, 16, 57] (normal_endpoints 1039) h]
    exact Submodule.zero_mem _
lemma extension_1040_30 : a k 30*normalRep k 1040=normalRep k 1128 := by
  exact (walk_snoc k 29 [37, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1040_31 : a k 31*normalRep k 1040=0 := by
  change a k 31*walk k 29 [37, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_833 (a k) (relation_zero k) (e k 29)
lemma arrow_span_1040 (b : Fin 75) : a k b*normalRep k 1040 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1040_30 k]
      exact normal_mem k 1128
    · rw [extension_1040_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1040=0 from arrow_incompatible k b 29 24 [37, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1040) h]
    exact Submodule.zero_mem _
lemma extension_1041_8 : a k 8*normalRep k 1041=normalRep k 1129 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_1041 (b : Fin 75) : a k b*normalRep k 1041 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1041_8 k]
      exact normal_mem k 1129
  · rw [show a k b*normalRep k 1041=0 from arrow_incompatible k b 30 8 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69] (normal_endpoints 1041) h]
    exact Submodule.zero_mem _
lemma extension_1042_72 : a k 72*normalRep k 1042=normalRep k 1130 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 71] 72).symm
lemma extension_1042_73 : a k 73*normalRep k 1042=normalRep k 1129 := by
  change a k 73*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 71]=walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_879 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1042 (b : Fin 75) : a k b*normalRep k 1042 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1042_72 k]
      exact normal_mem k 1130
    · rw [extension_1042_73 k]
      exact normal_mem k 1129
  · rw [show a k b*normalRep k 1042=0 from arrow_incompatible k b 30 44 [39, 12, 35, 55, 27, 58, 33, 13, 49, 71] (normal_endpoints 1042) h]
    exact Submodule.zero_mem _
lemma extension_1043_22 : a k 22*normalRep k 1043=normalRep k 1131 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 34, 63, 21, 70] 22).symm
lemma extension_1043_23 : a k 23*normalRep k 1043=normalRep k 1129 := by
  change a k 23*walk k 30 [39, 12, 35, 55, 27, 58, 34, 63, 21, 70]=walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_880 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1043 (b : Fin 75) : a k b*normalRep k 1043 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1043_22 k]
      exact normal_mem k 1131
    · rw [extension_1043_23 k]
      exact normal_mem k 1129
  · rw [show a k b*normalRep k 1043=0 from arrow_incompatible k b 30 19 [39, 12, 35, 55, 27, 58, 34, 63, 21, 70] (normal_endpoints 1043) h]
    exact Submodule.zero_mem _
lemma extension_1044_2 : a k 2*normalRep k 1044=normalRep k 1132 := by
  exact (walk_snoc k 30 [40, 60, 4, 54, 15, 1, 34, 63, 20, 30] 2).symm
lemma arrow_span_1044 (b : Fin 75) : a k b*normalRep k 1044 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1044_2 k]
      exact normal_mem k 1132
  · rw [show a k b*normalRep k 1044=0 from arrow_incompatible k b 30 2 [40, 60, 4, 54, 15, 1, 34, 63, 20, 30] (normal_endpoints 1044) h]
    exact Submodule.zero_mem _
lemma extension_1045_18 : a k 18*normalRep k 1045=normalRep k 1133 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24] 18).symm
lemma extension_1045_19 : a k 19*normalRep k 1045=normalRep k 1134 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24] 19).symm
lemma arrow_span_1045 (b : Fin 75) : a k b*normalRep k 1045 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1045_18 k]
      exact normal_mem k 1133
    · rw [extension_1045_19 k]
      exact normal_mem k 1134
  · rw [show a k b*normalRep k 1045=0 from arrow_incompatible k b 31 17 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24] (normal_endpoints 1045) h]
    exact Submodule.zero_mem _
lemma extension_1046_60 : a k 60*normalRep k 1046=normalRep k 1135 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 25] 60).symm
lemma extension_1046_61 : a k 61*normalRep k 1046=0 := by
  change a k 61*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_838 (a k) (relation_zero k) (e k 31)
lemma extension_1046_62 : a k 62*normalRep k 1046=normalRep k 1134 := by
  change a k 62*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 25]=walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_840 (a k) (relation_zero k) (e k 31)
lemma arrow_span_1046 (b : Fin 75) : a k b*normalRep k 1046 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1046_60 k]
      exact normal_mem k 1135
    · rw [extension_1046_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1046_62 k]
      exact normal_mem k 1134
  · rw [show a k b*normalRep k 1046=0 from arrow_incompatible k b 31 40 [41, 43, 47, 7, 17, 21, 69, 8, 66, 25] (normal_endpoints 1046) h]
    exact Submodule.zero_mem _
lemma extension_1047_14 : a k 14*normalRep k 1047=(-normalRep k 1133) := by
  change a k 14*walk k 31 [41, 43, 48, 51, 64, 36, 71, 72, 38, 28]=(-walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18])
  rw [← walk_snoc]
  exact Universal.mul_reduced_843 (a k) (relation_zero k) (e k 31)
lemma arrow_span_1047 (b : Fin 75) : a k b*normalRep k 1047 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1047_14 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1133)
  · rw [show a k b*normalRep k 1047=0 from arrow_incompatible k b 31 14 [41, 43, 48, 51, 64, 36, 71, 72, 38, 28] (normal_endpoints 1047) h]
    exact Submodule.zero_mem _
lemma extension_1048_9 : a k 9*normalRep k 1048=normalRep k 1136 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1048 (b : Fin 75) : a k b*normalRep k 1048 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1048_9 k]
      exact normal_mem k 1136
  · rw [show a k b*normalRep k 1048=0 from arrow_incompatible k b 32 9 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18] (normal_endpoints 1048) h]
    exact Submodule.zero_mem _
lemma extension_1049_52 : a k 52*normalRep k 1049=normalRep k 1136 := by
  change a k 52*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19]=walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_830 (a k) (relation_zero k) (e k 32)
lemma extension_1049_53 : a k 53*normalRep k 1049=normalRep k 1137 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1049 (b : Fin 75) : a k b*normalRep k 1049 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1049_52 k]
      exact normal_mem k 1136
    · rw [extension_1049_53 k]
      exact normal_mem k 1137
  · rw [show a k b*normalRep k 1049=0 from arrow_incompatible k b 32 37 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19] (normal_endpoints 1049) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
