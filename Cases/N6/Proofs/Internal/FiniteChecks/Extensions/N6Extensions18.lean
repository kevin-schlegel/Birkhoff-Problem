import N6NormalData
import N6Reduced11
import N6Reduced12
import N6Reduced13
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_900_41 : a k 41*normalRep k 900=normalRep k 997 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_900_42 : a k 42*normalRep k 900=0 := by
  change a k 42*walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_721 (a k) (relation_zero k) (e k 7)
lemma arrow_span_900 (b : Fin 75) : a k b*normalRep k 900 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_900_41 k]
      exact normal_mem k 997
    · rw [extension_900_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 900=0 from arrow_incompatible k b 7 31 [7, 17, 21, 69, 8, 66, 24, 18, 9] (normal_endpoints 900) h]
    exact Submodule.zero_mem _
lemma extension_901_54 : a k 54*normalRep k 901=normalRep k 998 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_901_55 : a k 55*normalRep k 901=0 := by
  change a k 55*walk k 7 [7, 17, 21, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_724 (a k) (relation_zero k) (e k 7)
lemma extension_901_56 : a k 56*normalRep k 901=normalRep k 997 := by
  change a k 56*walk k 7 [7, 17, 21, 69, 8, 66, 24, 19, 53]=walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_775 (a k) (relation_zero k) (e k 7)
lemma arrow_span_901 (b : Fin 75) : a k b*normalRep k 901 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_901_54 k]
      exact normal_mem k 998
    · rw [extension_901_55 k]
      exact Submodule.zero_mem _
    · rw [extension_901_56 k]
      exact normal_mem k 997
  · rw [show a k b*normalRep k 901=0 from arrow_incompatible k b 7 38 [7, 17, 21, 69, 8, 66, 24, 19, 53] (normal_endpoints 901) h]
    exact Submodule.zero_mem _
lemma extension_902_63 : a k 63*normalRep k 902=normalRep k 999 := by
  exact (walk_snoc k 8 [8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_902_64 : a k 64*normalRep k 902=0 := by
  change a k 64*walk k 8 [8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_716 (a k) (relation_zero k) (e k 8)
lemma extension_902_65 : a k 65*normalRep k 902=0 := by
  change a k 65*walk k 8 [8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_730 (a k) (relation_zero k) (e k 8)
lemma arrow_span_902 (b : Fin 75) : a k b*normalRep k 902 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_902_63 k]
      exact normal_mem k 999
    · rw [extension_902_64 k]
      exact Submodule.zero_mem _
    · rw [extension_902_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 902=0 from arrow_incompatible k b 8 41 [8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 902) h]
    exact Submodule.zero_mem _
lemma extension_903_0 : a k 0*normalRep k 903=normalRep k 1000 := by
  exact (walk_snoc k 9 [9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_903 (b : Fin 75) : a k b*normalRep k 903 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_903_0 k]
      exact normal_mem k 1000
  · rw [show a k b*normalRep k 903=0 from arrow_incompatible k b 9 0 [9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 903) h]
    exact Submodule.zero_mem _
lemma extension_904_54 : a k 54*normalRep k 904=0 := by
  change a k 54*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_763 (a k) (relation_zero k) (e k 10)
lemma extension_904_55 : a k 55*normalRep k 904=normalRep k 1001 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35] 55).symm
lemma extension_904_56 : a k 56*normalRep k 904=normalRep k 1002 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35] 56).symm
lemma arrow_span_904 (b : Fin 75) : a k b*normalRep k 904 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_904_54 k]
      exact Submodule.zero_mem _
    · rw [extension_904_55 k]
      exact normal_mem k 1001
    · rw [extension_904_56 k]
      exact normal_mem k 1002
  · rw [show a k b*normalRep k 904=0 from arrow_incompatible k b 10 38 [10, 11, 26, 31, 73, 67, 32, 61, 35] (normal_endpoints 904) h]
    exact Submodule.zero_mem _
lemma extension_905_41 : a k 41*normalRep k 905=normalRep k 1002 := by
  change a k 41*walk k 10 [10, 11, 26, 31, 73, 67, 32, 62, 52]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_776 (a k) (relation_zero k) (e k 10)
lemma extension_905_42 : a k 42*normalRep k 905=normalRep k 1003 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 62, 52] 42).symm
lemma arrow_span_905 (b : Fin 75) : a k b*normalRep k 905 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_905_41 k]
      exact normal_mem k 1002
    · rw [extension_905_42 k]
      exact normal_mem k 1003
  · rw [show a k b*normalRep k 905=0 from arrow_incompatible k b 10 31 [10, 11, 26, 31, 73, 67, 32, 62, 52] (normal_endpoints 905) h]
    exact Submodule.zero_mem _
lemma extension_906_27 : a k 27*normalRep k 906=normalRep k 1004 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55] 27).symm
lemma arrow_span_906 (b : Fin 75) : a k b*normalRep k 906 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_906_27 k]
      exact normal_mem k 1004
  · rw [show a k b*normalRep k 906=0 from arrow_incompatible k b 11 22 [11, 26, 31, 73, 67, 32, 61, 35, 55] (normal_endpoints 906) h]
    exact Submodule.zero_mem _
lemma extension_907_43 : a k 43*normalRep k 907=normalRep k 1005 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 56] 43).symm
lemma extension_907_44 : a k 44*normalRep k 907=normalRep k 1004 := by
  change a k 44*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 56]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27]
  rw [← walk_snoc]
  exact Universal.mul_reduced_779 (a k) (relation_zero k) (e k 11)
lemma arrow_span_907 (b : Fin 75) : a k b*normalRep k 907 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_907_43 k]
      exact normal_mem k 1005
    · rw [extension_907_44 k]
      exact normal_mem k 1004
  · rw [show a k b*normalRep k 907=0 from arrow_incompatible k b 11 32 [11, 26, 31, 73, 67, 32, 61, 35, 56] (normal_endpoints 907) h]
    exact Submodule.zero_mem _
lemma extension_908_45 : a k 45*normalRep k 908=normalRep k 1006 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 62, 52, 42] 45).symm
lemma extension_908_46 : a k 46*normalRep k 908=normalRep k 1005 := by
  change a k 46*walk k 11 [11, 26, 31, 73, 67, 32, 62, 52, 42]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 56, 43]
  rw [← walk_snoc]
  exact Universal.mul_reduced_768 (a k) (relation_zero k) (e k 11)
lemma arrow_span_908 (b : Fin 75) : a k b*normalRep k 908 ∈ normalSpan k := by
  by_cases h : arrowSource b=33
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [45, 46] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_908_45 k]
      exact normal_mem k 1006
    · rw [extension_908_46 k]
      exact normal_mem k 1005
  · rw [show a k b*normalRep k 908=0 from arrow_incompatible k b 11 33 [11, 26, 31, 73, 67, 32, 62, 52, 42] (normal_endpoints 908) h]
    exact Submodule.zero_mem _
lemma extension_909_8 : a k 8*normalRep k 909=normalRep k 1007 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_909 (b : Fin 75) : a k b*normalRep k 909 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_909_8 k]
      exact normal_mem k 1007
  · rw [show a k b*normalRep k 909=0 from arrow_incompatible k b 12 8 [12, 35, 55, 27, 58, 33, 13, 49, 69] (normal_endpoints 909) h]
    exact Submodule.zero_mem _
lemma extension_910_72 : a k 72*normalRep k 910=normalRep k 1008 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 71] 72).symm
lemma extension_910_73 : a k 73*normalRep k 910=normalRep k 1007 := by
  change a k 73*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 71]=walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_796 (a k) (relation_zero k) (e k 12)
lemma arrow_span_910 (b : Fin 75) : a k b*normalRep k 910 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_910_72 k]
      exact normal_mem k 1008
    · rw [extension_910_73 k]
      exact normal_mem k 1007
  · rw [show a k b*normalRep k 910=0 from arrow_incompatible k b 12 44 [12, 35, 55, 27, 58, 33, 13, 49, 71] (normal_endpoints 910) h]
    exact Submodule.zero_mem _
lemma extension_911_22 : a k 22*normalRep k 911=normalRep k 1009 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 34, 63, 21, 70] 22).symm
lemma extension_911_23 : a k 23*normalRep k 911=normalRep k 1007 := by
  change a k 23*walk k 12 [12, 35, 55, 27, 58, 34, 63, 21, 70]=walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_797 (a k) (relation_zero k) (e k 12)
lemma arrow_span_911 (b : Fin 75) : a k b*normalRep k 911 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_911_22 k]
      exact normal_mem k 1009
    · rw [extension_911_23 k]
      exact normal_mem k 1007
  · rw [show a k b*normalRep k 911=0 from arrow_incompatible k b 12 19 [12, 35, 55, 27, 58, 34, 63, 21, 70] (normal_endpoints 911) h]
    exact Submodule.zero_mem _
lemma extension_912_43 : a k 43*normalRep k 912=0 := by
  change a k 43*walk k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_727 (a k) (relation_zero k) (e k 13)
lemma extension_912_44 : a k 44*normalRep k 912=normalRep k 1010 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_912 (b : Fin 75) : a k b*normalRep k 912 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_912_43 k]
      exact Submodule.zero_mem _
    · rw [extension_912_44 k]
      exact normal_mem k 1010
  · rw [show a k b*normalRep k 912=0 from arrow_incompatible k b 13 32 [13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 912) h]
    exact Submodule.zero_mem _
lemma extension_913_15 : a k 15*normalRep k 913=normalRep k 1011 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_913_16 : a k 16*normalRep k 913=normalRep k 1010 := by
  change a k 16*walk k 13 [13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_780 (a k) (relation_zero k) (e k 13)
lemma arrow_span_913 (b : Fin 75) : a k b*normalRep k 913 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_913_15 k]
      exact normal_mem k 1011
    · rw [extension_913_16 k]
      exact normal_mem k 1010
  · rw [show a k b*normalRep k 913=0 from arrow_incompatible k b 13 15 [13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 913) h]
    exact Submodule.zero_mem _
lemma extension_914_2 : a k 2*normalRep k 914=normalRep k 1012 := by
  exact (walk_snoc k 14 [14, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_914 (b : Fin 75) : a k b*normalRep k 914 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_914_2 k]
      exact normal_mem k 1012
  · rw [show a k b*normalRep k 914=0 from arrow_incompatible k b 14 2 [14, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 914) h]
    exact Submodule.zero_mem _
lemma extension_915_43 : a k 43*normalRep k 915=0 := by
  change a k 43*walk k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_728 (a k) (relation_zero k) (e k 16)
lemma extension_915_44 : a k 44*normalRep k 915=normalRep k 1013 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_915 (b : Fin 75) : a k b*normalRep k 915 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_915_43 k]
      exact Submodule.zero_mem _
    · rw [extension_915_44 k]
      exact normal_mem k 1013
  · rw [show a k b*normalRep k 915=0 from arrow_incompatible k b 16 32 [17, 21, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 915) h]
    exact Submodule.zero_mem _
lemma extension_916_15 : a k 15*normalRep k 916=normalRep k 1014 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_916_16 : a k 16*normalRep k 916=normalRep k 1013 := by
  change a k 16*walk k 16 [17, 21, 69, 8, 66, 24, 19, 53, 54]=walk k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_781 (a k) (relation_zero k) (e k 16)
lemma arrow_span_916 (b : Fin 75) : a k b*normalRep k 916 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_916_15 k]
      exact normal_mem k 1014
    · rw [extension_916_16 k]
      exact normal_mem k 1013
  · rw [show a k b*normalRep k 916=0 from arrow_incompatible k b 16 15 [17, 21, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 916) h]
    exact Submodule.zero_mem _
lemma extension_917_2 : a k 2*normalRep k 917=normalRep k 1015 := by
  exact (walk_snoc k 17 [18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_917 (b : Fin 75) : a k b*normalRep k 917 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_917_2 k]
      exact normal_mem k 1015
  · rw [show a k b*normalRep k 917=0 from arrow_incompatible k b 17 2 [18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 917) h]
    exact Submodule.zero_mem _
lemma extension_918_57 : a k 57*normalRep k 918=normalRep k 1016 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_918_58 : a k 58*normalRep k 918=normalRep k 1017 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_918_59 : a k 59*normalRep k 918=0 := by
  change a k 59*walk k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_738 (a k) (relation_zero k) (e k 18)
lemma arrow_span_918 (b : Fin 75) : a k b*normalRep k 918 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_918_57 k]
      exact normal_mem k 1016
    · rw [extension_918_58 k]
      exact normal_mem k 1017
    · rw [extension_918_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 918=0 from arrow_incompatible k b 18 39 [21, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 918) h]
    exact Submodule.zero_mem _
lemma extension_919_1 : a k 1*normalRep k 919=normalRep k 1017 := by
  change a k 1*walk k 18 [21, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_735 (a k) (relation_zero k) (e k 18)
lemma arrow_span_919 (b : Fin 75) : a k b*normalRep k 919 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_919_1 k]
      exact normal_mem k 1017
  · rw [show a k b*normalRep k 919=0 from arrow_incompatible k b 18 1 [21, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 919) h]
    exact Submodule.zero_mem _
lemma extension_920_63 : a k 63*normalRep k 920=normalRep k 1018 := by
  exact (walk_snoc k 19 [22, 3, 40, 60, 4, 54, 15, 1, 34] 63).symm
lemma extension_920_64 : a k 64*normalRep k 920=0 := by
  change a k 64*walk k 19 [22, 3, 40, 60, 4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_717 (a k) (relation_zero k) (e k 19)
lemma extension_920_65 : a k 65*normalRep k 920=0 := by
  change a k 65*walk k 19 [22, 3, 40, 60, 4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_731 (a k) (relation_zero k) (e k 19)
lemma arrow_span_920 (b : Fin 75) : a k b*normalRep k 920 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_920_63 k]
      exact normal_mem k 1018
    · rw [extension_920_64 k]
      exact Submodule.zero_mem _
    · rw [extension_920_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 920=0 from arrow_incompatible k b 19 41 [22, 3, 40, 60, 4, 54, 15, 1, 34] (normal_endpoints 920) h]
    exact Submodule.zero_mem _
lemma extension_921_30 : a k 30*normalRep k 921=normalRep k 1019 := by
  exact (walk_snoc k 20 [24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_921_31 : a k 31*normalRep k 921=0 := by
  change a k 31*walk k 20 [24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_745 (a k) (relation_zero k) (e k 20)
lemma arrow_span_921 (b : Fin 75) : a k b*normalRep k 921 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_921_30 k]
      exact normal_mem k 1019
    · rw [extension_921_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 921=0 from arrow_incompatible k b 20 24 [24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 921) h]
    exact Submodule.zero_mem _
lemma extension_922_57 : a k 57*normalRep k 922=0 := by
  change a k 57*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_758 (a k) (relation_zero k) (e k 21)
lemma extension_922_58 : a k 58*normalRep k 922=normalRep k 1020 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27] 58).symm
lemma extension_922_59 : a k 59*normalRep k 922=normalRep k 1021 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27] 59).symm
lemma arrow_span_922 (b : Fin 75) : a k b*normalRep k 922 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_922_57 k]
      exact Submodule.zero_mem _
    · rw [extension_922_58 k]
      exact normal_mem k 1020
    · rw [extension_922_59 k]
      exact normal_mem k 1021
  · rw [show a k b*normalRep k 922=0 from arrow_incompatible k b 21 39 [26, 31, 73, 67, 32, 61, 35, 55, 27] (normal_endpoints 922) h]
    exact Submodule.zero_mem _
lemma extension_923_47 : a k 47*normalRep k 923=normalRep k 1022 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 56, 43] 47).symm
lemma extension_923_48 : a k 48*normalRep k 923=normalRep k 1021 := by
  change a k 48*walk k 21 [26, 31, 73, 67, 32, 61, 35, 56, 43]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 59]
  rw [← walk_snoc]
  exact Universal.mul_reduced_769 (a k) (relation_zero k) (e k 21)
lemma arrow_span_923 (b : Fin 75) : a k b*normalRep k 923 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_923_47 k]
      exact normal_mem k 1022
    · rw [extension_923_48 k]
      exact normal_mem k 1021
  · rw [show a k b*normalRep k 923=0 from arrow_incompatible k b 21 34 [26, 31, 73, 67, 32, 61, 35, 56, 43] (normal_endpoints 923) h]
    exact Submodule.zero_mem _
lemma extension_924_6 : a k 6*normalRep k 924=normalRep k 1022 := by
  change a k 6*walk k 21 [26, 31, 73, 67, 32, 62, 52, 42, 45]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 56, 43, 47]
  rw [← walk_snoc]
  exact Universal.mul_reduced_770 (a k) (relation_zero k) (e k 21)
lemma arrow_span_924 (b : Fin 75) : a k b*normalRep k 924 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_924_6 k]
      exact normal_mem k 1022
  · rw [show a k b*normalRep k 924=0 from arrow_incompatible k b 21 6 [26, 31, 73, 67, 32, 62, 52, 42, 45] (normal_endpoints 924) h]
    exact Submodule.zero_mem _
lemma extension_925_18 : a k 18*normalRep k 925=normalRep k 1023 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_925_19 : a k 19*normalRep k 925=normalRep k 1024 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_925 (b : Fin 75) : a k b*normalRep k 925 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_925_18 k]
      exact normal_mem k 1023
    · rw [extension_925_19 k]
      exact normal_mem k 1024
  · rw [show a k b*normalRep k 925=0 from arrow_incompatible k b 22 17 [27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 925) h]
    exact Submodule.zero_mem _
lemma extension_926_60 : a k 60*normalRep k 926=normalRep k 1025 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_926_61 : a k 61*normalRep k 926=0 := by
  change a k 61*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_752 (a k) (relation_zero k) (e k 22)
lemma extension_926_62 : a k 62*normalRep k 926=normalRep k 1024 := by
  change a k 62*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_755 (a k) (relation_zero k) (e k 22)
lemma arrow_span_926 (b : Fin 75) : a k b*normalRep k 926 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_926_60 k]
      exact normal_mem k 1025
    · rw [extension_926_61 k]
      exact Submodule.zero_mem _
    · rw [extension_926_62 k]
      exact normal_mem k 1024
  · rw [show a k b*normalRep k 926=0 from arrow_incompatible k b 22 40 [27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 926) h]
    exact Submodule.zero_mem _
lemma extension_927_14 : a k 14*normalRep k 927=normalRep k 1023 := by
  change a k 14*walk k 22 [27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_759 (a k) (relation_zero k) (e k 22)
lemma arrow_span_927 (b : Fin 75) : a k b*normalRep k 927 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_927_14 k]
      exact normal_mem k 1023
  · rw [show a k b*normalRep k 927=0 from arrow_incompatible k b 22 14 [27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 927) h]
    exact Submodule.zero_mem _
lemma extension_928_30 : a k 30*normalRep k 928=normalRep k 1026 := by
  exact (walk_snoc k 23 [28, 14, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_928_31 : a k 31*normalRep k 928=0 := by
  change a k 31*walk k 23 [28, 14, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_746 (a k) (relation_zero k) (e k 23)
lemma arrow_span_928 (b : Fin 75) : a k b*normalRep k 928 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_928_30 k]
      exact normal_mem k 1026
    · rw [extension_928_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 928=0 from arrow_incompatible k b 23 24 [28, 14, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 928) h]
    exact Submodule.zero_mem _
lemma extension_929_33 : a k 33*normalRep k 929=normalRep k 1027 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58] 33).symm
lemma extension_929_34 : a k 34*normalRep k 929=normalRep k 1028 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58] 34).symm
lemma arrow_span_929 (b : Fin 75) : a k b*normalRep k 929 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_929_33 k]
      exact normal_mem k 1027
    · rw [extension_929_34 k]
      exact normal_mem k 1028
  · rw [show a k b*normalRep k 929=0 from arrow_incompatible k b 24 26 [31, 73, 67, 32, 61, 35, 55, 27, 58] (normal_endpoints 929) h]
    exact Submodule.zero_mem _
lemma extension_930_50 : a k 50*normalRep k 930=normalRep k 1029 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 59] 50).symm
lemma extension_930_51 : a k 51*normalRep k 930=normalRep k 1028 := by
  change a k 51*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 59]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_783 (a k) (relation_zero k) (e k 24)
lemma arrow_span_930 (b : Fin 75) : a k b*normalRep k 930 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_930_50 k]
      exact normal_mem k 1029
    · rw [extension_930_51 k]
      exact normal_mem k 1028
  · rw [show a k b*normalRep k 930=0 from arrow_incompatible k b 24 36 [31, 73, 67, 32, 61, 35, 55, 27, 59] (normal_endpoints 930) h]
    exact Submodule.zero_mem _
lemma extension_931_7 : a k 7*normalRep k 931=normalRep k 1029 := by
  change a k 7*walk k 24 [31, 73, 67, 32, 61, 35, 56, 43, 47]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 59, 50]
  rw [← walk_snoc]
  exact Universal.mul_reduced_771 (a k) (relation_zero k) (e k 24)
lemma arrow_span_931 (b : Fin 75) : a k b*normalRep k 931 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_931_7 k]
      exact normal_mem k 1029
  · rw [show a k b*normalRep k 931=0 from arrow_incompatible k b 24 7 [31, 73, 67, 32, 61, 35, 56, 43, 47] (normal_endpoints 931) h]
    exact Submodule.zero_mem _
lemma extension_932_69 : a k 69*normalRep k 932=normalRep k 1030 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49] 69).symm
lemma extension_932_70 : a k 70*normalRep k 932=0 := by
  change a k 70*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_772 (a k) (relation_zero k) (e k 25)
lemma extension_932_71 : a k 71*normalRep k 932=normalRep k 1031 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49] 71).symm
lemma arrow_span_932 (b : Fin 75) : a k b*normalRep k 932 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_932_69 k]
      exact normal_mem k 1030
    · rw [extension_932_70 k]
      exact Submodule.zero_mem _
    · rw [extension_932_71 k]
      exact normal_mem k 1031
  · rw [show a k b*normalRep k 932=0 from arrow_incompatible k b 25 43 [32, 61, 35, 55, 27, 58, 33, 13, 49] (normal_endpoints 932) h]
    exact Submodule.zero_mem _
lemma extension_933_69 : a k 69*normalRep k 933=(-normalRep k 1030) := by
  change a k 69*walk k 25 [32, 61, 35, 55, 27, 58, 34, 63, 21]=(-walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_764 (a k) (relation_zero k) (e k 25)
lemma extension_933_70 : a k 70*normalRep k 933=normalRep k 1032 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 34, 63, 21] 70).symm
lemma extension_933_71 : a k 71*normalRep k 933=0 := by
  change a k 71*walk k 25 [32, 61, 35, 55, 27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_748 (a k) (relation_zero k) (e k 25)
lemma arrow_span_933 (b : Fin 75) : a k b*normalRep k 933 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_933_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1030)
    · rw [extension_933_70 k]
      exact normal_mem k 1032
    · rw [extension_933_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 933=0 from arrow_incompatible k b 25 43 [32, 61, 35, 55, 27, 58, 34, 63, 21] (normal_endpoints 933) h]
    exact Submodule.zero_mem _
lemma extension_934_41 : a k 41*normalRep k 934=normalRep k 1033 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_934_42 : a k 42*normalRep k 934=0 := by
  change a k 42*walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_722 (a k) (relation_zero k) (e k 26)
lemma arrow_span_934 (b : Fin 75) : a k b*normalRep k 934 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_934_41 k]
      exact normal_mem k 1033
    · rw [extension_934_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 934=0 from arrow_incompatible k b 26 31 [33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 934) h]
    exact Submodule.zero_mem _
lemma extension_935_54 : a k 54*normalRep k 935=normalRep k 1034 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_935_55 : a k 55*normalRep k 935=0 := by
  change a k 55*walk k 26 [33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_725 (a k) (relation_zero k) (e k 26)
lemma extension_935_56 : a k 56*normalRep k 935=normalRep k 1033 := by
  change a k 56*walk k 26 [33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_777 (a k) (relation_zero k) (e k 26)
lemma arrow_span_935 (b : Fin 75) : a k b*normalRep k 935 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_935_54 k]
      exact normal_mem k 1034
    · rw [extension_935_55 k]
      exact Submodule.zero_mem _
    · rw [extension_935_56 k]
      exact normal_mem k 1033
  · rw [show a k b*normalRep k 935=0 from arrow_incompatible k b 26 38 [33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 935) h]
    exact Submodule.zero_mem _
lemma extension_936_66 : a k 66*normalRep k 936=normalRep k 1035 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_936_67 : a k 67*normalRep k 936=0 := by
  change a k 67*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_733 (a k) (relation_zero k) (e k 27)
lemma extension_936_68 : a k 68*normalRep k 936=normalRep k 1036 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_936 (b : Fin 75) : a k b*normalRep k 936 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_936_66 k]
      exact normal_mem k 1035
    · rw [extension_936_67 k]
      exact Submodule.zero_mem _
    · rw [extension_936_68 k]
      exact normal_mem k 1036
  · rw [show a k b*normalRep k 936=0 from arrow_incompatible k b 27 42 [35, 55, 27, 58, 33, 13, 49, 69, 8] (normal_endpoints 936) h]
    exact Submodule.zero_mem _
lemma extension_937_37 : a k 37*normalRep k 937=normalRep k 1035 := by
  change a k 37*walk k 27 [35, 55, 27, 58, 33, 13, 49, 71, 72]=walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_800 (a k) (relation_zero k) (e k 27)
lemma extension_937_38 : a k 38*normalRep k 937=normalRep k 1037 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_937 (b : Fin 75) : a k b*normalRep k 937 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_937_37 k]
      exact normal_mem k 1035
    · rw [extension_937_38 k]
      exact normal_mem k 1037
  · rw [show a k b*normalRep k 937=0 from arrow_incompatible k b 27 29 [35, 55, 27, 58, 33, 13, 49, 71, 72] (normal_endpoints 937) h]
    exact Submodule.zero_mem _
lemma extension_938_3 : a k 3*normalRep k 938=(-normalRep k 1036) := by
  change a k 3*walk k 27 [35, 55, 27, 58, 34, 63, 21, 70, 22]=(-walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_750 (a k) (relation_zero k) (e k 27)
lemma arrow_span_938 (b : Fin 75) : a k b*normalRep k 938 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_938_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1036)
  · rw [show a k b*normalRep k 938=0 from arrow_incompatible k b 27 3 [35, 55, 27, 58, 34, 63, 21, 70, 22] (normal_endpoints 938) h]
    exact Submodule.zero_mem _
lemma extension_939_1 : a k 1*normalRep k 939=normalRep k 1038 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15] 1).symm
lemma arrow_span_939 (b : Fin 75) : a k b*normalRep k 939 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_939_1 k]
      exact normal_mem k 1038
  · rw [show a k b*normalRep k 939=0 from arrow_incompatible k b 28 1 [36, 70, 22, 3, 40, 60, 4, 54, 15] (normal_endpoints 939) h]
    exact Submodule.zero_mem _
lemma extension_940_57 : a k 57*normalRep k 940=normalRep k 1039 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 60, 4, 54, 16] 57).symm
lemma extension_940_58 : a k 58*normalRep k 940=normalRep k 1038 := by
  change a k 58*walk k 28 [36, 70, 22, 3, 40, 60, 4, 54, 16]=walk k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1]
  rw [← walk_snoc]
  exact Universal.mul_reduced_736 (a k) (relation_zero k) (e k 28)
lemma extension_940_59 : a k 59*normalRep k 940=0 := by
  change a k 59*walk k 28 [36, 70, 22, 3, 40, 60, 4, 54, 16]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_739 (a k) (relation_zero k) (e k 28)
lemma arrow_span_940 (b : Fin 75) : a k b*normalRep k 940 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_940_57 k]
      exact normal_mem k 1039
    · rw [extension_940_58 k]
      exact normal_mem k 1038
    · rw [extension_940_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 940=0 from arrow_incompatible k b 28 39 [36, 70, 22, 3, 40, 60, 4, 54, 16] (normal_endpoints 940) h]
    exact Submodule.zero_mem _
lemma extension_941_20 : a k 20*normalRep k 941=normalRep k 1040 := by
  exact (walk_snoc k 29 [37, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_941_21 : a k 21*normalRep k 941=0 := by
  change a k 21*walk k 29 [37, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_791 (a k) (relation_zero k) (e k 29)
lemma arrow_span_941 (b : Fin 75) : a k b*normalRep k 941 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_941_20 k]
      exact normal_mem k 1040
    · rw [extension_941_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 941=0 from arrow_incompatible k b 29 18 [37, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 941) h]
    exact Submodule.zero_mem _
lemma extension_942_69 : a k 69*normalRep k 942=normalRep k 1041 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49] 69).symm
lemma extension_942_70 : a k 70*normalRep k 942=0 := by
  change a k 70*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_773 (a k) (relation_zero k) (e k 30)
lemma extension_942_71 : a k 71*normalRep k 942=normalRep k 1042 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49] 71).symm
lemma arrow_span_942 (b : Fin 75) : a k b*normalRep k 942 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_942_69 k]
      exact normal_mem k 1041
    · rw [extension_942_70 k]
      exact Submodule.zero_mem _
    · rw [extension_942_71 k]
      exact normal_mem k 1042
  · rw [show a k b*normalRep k 942=0 from arrow_incompatible k b 30 43 [39, 12, 35, 55, 27, 58, 33, 13, 49] (normal_endpoints 942) h]
    exact Submodule.zero_mem _
lemma extension_943_69 : a k 69*normalRep k 943=(-normalRep k 1041) := by
  change a k 69*walk k 30 [39, 12, 35, 55, 27, 58, 34, 63, 21]=(-walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_765 (a k) (relation_zero k) (e k 30)
lemma extension_943_70 : a k 70*normalRep k 943=normalRep k 1043 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 34, 63, 21] 70).symm
lemma extension_943_71 : a k 71*normalRep k 943=0 := by
  change a k 71*walk k 30 [39, 12, 35, 55, 27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_749 (a k) (relation_zero k) (e k 30)
lemma arrow_span_943 (b : Fin 75) : a k b*normalRep k 943 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_943_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1041)
    · rw [extension_943_70 k]
      exact normal_mem k 1043
    · rw [extension_943_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 943=0 from arrow_incompatible k b 30 43 [39, 12, 35, 55, 27, 58, 34, 63, 21] (normal_endpoints 943) h]
    exact Submodule.zero_mem _
lemma extension_944_30 : a k 30*normalRep k 944=normalRep k 1044 := by
  exact (walk_snoc k 30 [40, 60, 4, 54, 15, 1, 34, 63, 20] 30).symm
lemma extension_944_31 : a k 31*normalRep k 944=0 := by
  change a k 31*walk k 30 [40, 60, 4, 54, 15, 1, 34, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_747 (a k) (relation_zero k) (e k 30)
lemma arrow_span_944 (b : Fin 75) : a k b*normalRep k 944 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_944_30 k]
      exact normal_mem k 1044
    · rw [extension_944_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 944=0 from arrow_incompatible k b 30 24 [40, 60, 4, 54, 15, 1, 34, 63, 20] (normal_endpoints 944) h]
    exact Submodule.zero_mem _
lemma extension_945_24 : a k 24*normalRep k 945=normalRep k 1045 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66] 24).symm
lemma extension_945_25 : a k 25*normalRep k 945=normalRep k 1046 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66] 25).symm
lemma arrow_span_945 (b : Fin 75) : a k b*normalRep k 945 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_945_24 k]
      exact normal_mem k 1045
    · rw [extension_945_25 k]
      exact normal_mem k 1046
  · rw [show a k b*normalRep k 945=0 from arrow_incompatible k b 31 20 [41, 43, 47, 7, 17, 21, 69, 8, 66] (normal_endpoints 945) h]
    exact Submodule.zero_mem _
lemma extension_946_39 : a k 39*normalRep k 946=0 := by
  change a k 39*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_719 (a k) (relation_zero k) (e k 31)
lemma extension_946_40 : a k 40*normalRep k 946=(-normalRep k 1046) := by
  change a k 40*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 68]=(-walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_794 (a k) (relation_zero k) (e k 31)
lemma arrow_span_946 (b : Fin 75) : a k b*normalRep k 946 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_946_39 k]
      exact Submodule.zero_mem _
    · rw [extension_946_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1046)
  · rw [show a k b*normalRep k 946=0 from arrow_incompatible k b 31 30 [41, 43, 47, 7, 17, 21, 69, 8, 68] (normal_endpoints 946) h]
    exact Submodule.zero_mem _
lemma extension_947_28 : a k 28*normalRep k 947=normalRep k 1047 := by
  exact (walk_snoc k 31 [41, 43, 48, 51, 64, 36, 71, 72, 38] 28).symm
lemma extension_947_29 : a k 29*normalRep k 947=(-normalRep k 1045) := by
  change a k 29*walk k 31 [41, 43, 48, 51, 64, 36, 71, 72, 38]=(-walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24])
  rw [← walk_snoc]
  exact Universal.mul_reduced_766 (a k) (relation_zero k) (e k 31)
lemma arrow_span_947 (b : Fin 75) : a k b*normalRep k 947 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_947_28 k]
      exact normal_mem k 1047
    · rw [extension_947_29 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1045)
  · rw [show a k b*normalRep k 947=0 from arrow_incompatible k b 31 23 [41, 43, 48, 51, 64, 36, 71, 72, 38] (normal_endpoints 947) h]
    exact Submodule.zero_mem _
lemma arrow_span_948 (b : Fin 75) : a k b*normalRep k 948 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 948=0 from arrow_incompatible k b 31 46 [41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 948) h]
    exact Submodule.zero_mem _
lemma extension_949_18 : a k 18*normalRep k 949=normalRep k 1048 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24] 18).symm
lemma extension_949_19 : a k 19*normalRep k 949=normalRep k 1049 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24] 19).symm
lemma arrow_span_949 (b : Fin 75) : a k b*normalRep k 949 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_949_18 k]
      exact normal_mem k 1048
    · rw [extension_949_19 k]
      exact normal_mem k 1049
  · rw [show a k b*normalRep k 949=0 from arrow_incompatible k b 32 17 [43, 47, 7, 17, 21, 69, 8, 66, 24] (normal_endpoints 949) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
