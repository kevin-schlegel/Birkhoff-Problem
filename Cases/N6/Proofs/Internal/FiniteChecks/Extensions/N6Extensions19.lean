import N6NormalData
import N6Reduced11
import N6Reduced12
import N6Reduced13
import N6Reduced14
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_950_60 : a k 60*normalRep k 950=normalRep k 1050 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 25] 60).symm
lemma extension_950_61 : a k 61*normalRep k 950=0 := by
  change a k 61*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_753 (a k) (relation_zero k) (e k 32)
lemma extension_950_62 : a k 62*normalRep k 950=normalRep k 1049 := by
  change a k 62*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 25]=walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_756 (a k) (relation_zero k) (e k 32)
lemma arrow_span_950 (b : Fin 75) : a k b*normalRep k 950 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_950_60 k]
      exact normal_mem k 1050
    · rw [extension_950_61 k]
      exact Submodule.zero_mem _
    · rw [extension_950_62 k]
      exact normal_mem k 1049
  · rw [show a k b*normalRep k 950=0 from arrow_incompatible k b 32 40 [43, 47, 7, 17, 21, 69, 8, 66, 25] (normal_endpoints 950) h]
    exact Submodule.zero_mem _
lemma extension_951_14 : a k 14*normalRep k 951=(-normalRep k 1048) := by
  change a k 14*walk k 32 [43, 48, 51, 64, 36, 71, 72, 38, 28]=(-walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18])
  rw [← walk_snoc]
  exact Universal.mul_reduced_760 (a k) (relation_zero k) (e k 32)
lemma arrow_span_951 (b : Fin 75) : a k b*normalRep k 951 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_951_14 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1048)
  · rw [show a k b*normalRep k 951=0 from arrow_incompatible k b 32 14 [43, 48, 51, 64, 36, 71, 72, 38, 28] (normal_endpoints 951) h]
    exact Submodule.zero_mem _
lemma extension_952_18 : a k 18*normalRep k 952=normalRep k 1051 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24] 18).symm
lemma extension_952_19 : a k 19*normalRep k 952=normalRep k 1052 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24] 19).symm
lemma arrow_span_952 (b : Fin 75) : a k b*normalRep k 952 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_952_18 k]
      exact normal_mem k 1051
    · rw [extension_952_19 k]
      exact normal_mem k 1052
  · rw [show a k b*normalRep k 952=0 from arrow_incompatible k b 33 17 [45, 6, 7, 17, 21, 69, 8, 66, 24] (normal_endpoints 952) h]
    exact Submodule.zero_mem _
lemma extension_953_60 : a k 60*normalRep k 953=normalRep k 1053 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 25] 60).symm
lemma extension_953_61 : a k 61*normalRep k 953=0 := by
  change a k 61*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_754 (a k) (relation_zero k) (e k 33)
lemma extension_953_62 : a k 62*normalRep k 953=normalRep k 1052 := by
  change a k 62*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 25]=walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_757 (a k) (relation_zero k) (e k 33)
lemma arrow_span_953 (b : Fin 75) : a k b*normalRep k 953 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_953_60 k]
      exact normal_mem k 1053
    · rw [extension_953_61 k]
      exact Submodule.zero_mem _
    · rw [extension_953_62 k]
      exact normal_mem k 1052
  · rw [show a k b*normalRep k 953=0 from arrow_incompatible k b 33 40 [45, 6, 7, 17, 21, 69, 8, 66, 25] (normal_endpoints 953) h]
    exact Submodule.zero_mem _
lemma extension_954_14 : a k 14*normalRep k 954=(-normalRep k 1051) := by
  change a k 14*walk k 33 [46, 48, 51, 64, 36, 71, 72, 38, 28]=(-walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18])
  rw [← walk_snoc]
  exact Universal.mul_reduced_761 (a k) (relation_zero k) (e k 33)
lemma arrow_span_954 (b : Fin 75) : a k b*normalRep k 954 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_954_14 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1051)
  · rw [show a k b*normalRep k 954=0 from arrow_incompatible k b 33 14 [46, 48, 51, 64, 36, 71, 72, 38, 28] (normal_endpoints 954) h]
    exact Submodule.zero_mem _
lemma extension_955_9 : a k 9*normalRep k 955=normalRep k 1054 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_955 (b : Fin 75) : a k b*normalRep k 955 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_955_9 k]
      exact normal_mem k 1054
  · rw [show a k b*normalRep k 955=0 from arrow_incompatible k b 34 9 [47, 7, 17, 21, 69, 8, 66, 24, 18] (normal_endpoints 955) h]
    exact Submodule.zero_mem _
lemma extension_956_52 : a k 52*normalRep k 956=normalRep k 1054 := by
  change a k 52*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 19]=walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_743 (a k) (relation_zero k) (e k 34)
lemma extension_956_53 : a k 53*normalRep k 956=normalRep k 1055 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_956 (b : Fin 75) : a k b*normalRep k 956 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_956_52 k]
      exact normal_mem k 1054
    · rw [extension_956_53 k]
      exact normal_mem k 1055
  · rw [show a k b*normalRep k 956=0 from arrow_incompatible k b 34 37 [47, 7, 17, 21, 69, 8, 66, 24, 19] (normal_endpoints 956) h]
    exact Submodule.zero_mem _
lemma extension_957_4 : a k 4*normalRep k 957=normalRep k 1055 := by
  change a k 4*walk k 34 [47, 7, 17, 21, 69, 8, 66, 25, 60]=walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_787 (a k) (relation_zero k) (e k 34)
lemma arrow_span_957 (b : Fin 75) : a k b*normalRep k 957 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_957_4 k]
      exact normal_mem k 1055
  · rw [show a k b*normalRep k 957=0 from arrow_incompatible k b 34 4 [47, 7, 17, 21, 69, 8, 66, 25, 60] (normal_endpoints 957) h]
    exact Submodule.zero_mem _
lemma extension_958_57 : a k 57*normalRep k 958=normalRep k 1056 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_958_58 : a k 58*normalRep k 958=normalRep k 1057 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_958_59 : a k 59*normalRep k 958=0 := by
  change a k 59*walk k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_740 (a k) (relation_zero k) (e k 35)
lemma arrow_span_958 (b : Fin 75) : a k b*normalRep k 958 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_958_57 k]
      exact normal_mem k 1056
    · rw [extension_958_58 k]
      exact normal_mem k 1057
    · rw [extension_958_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 958=0 from arrow_incompatible k b 35 39 [49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 958) h]
    exact Submodule.zero_mem _
lemma extension_959_1 : a k 1*normalRep k 959=normalRep k 1057 := by
  change a k 1*walk k 35 [49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_737 (a k) (relation_zero k) (e k 35)
lemma arrow_span_959 (b : Fin 75) : a k b*normalRep k 959 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_959_1 k]
      exact normal_mem k 1057
  · rw [show a k b*normalRep k 959=0 from arrow_incompatible k b 35 1 [49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 959) h]
    exact Submodule.zero_mem _
lemma extension_960_41 : a k 41*normalRep k 960=normalRep k 1058 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_960_42 : a k 42*normalRep k 960=0 := by
  change a k 42*walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_723 (a k) (relation_zero k) (e k 36)
lemma arrow_span_960 (b : Fin 75) : a k b*normalRep k 960 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_960_41 k]
      exact normal_mem k 1058
    · rw [extension_960_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 960=0 from arrow_incompatible k b 36 31 [50, 17, 21, 69, 8, 66, 24, 18, 9] (normal_endpoints 960) h]
    exact Submodule.zero_mem _
lemma extension_961_54 : a k 54*normalRep k 961=normalRep k 1059 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_961_55 : a k 55*normalRep k 961=0 := by
  change a k 55*walk k 36 [50, 17, 21, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_726 (a k) (relation_zero k) (e k 36)
lemma extension_961_56 : a k 56*normalRep k 961=normalRep k 1058 := by
  change a k 56*walk k 36 [50, 17, 21, 69, 8, 66, 24, 19, 53]=walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_778 (a k) (relation_zero k) (e k 36)
lemma arrow_span_961 (b : Fin 75) : a k b*normalRep k 961 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_961_54 k]
      exact normal_mem k 1059
    · rw [extension_961_55 k]
      exact Submodule.zero_mem _
    · rw [extension_961_56 k]
      exact normal_mem k 1058
  · rw [show a k b*normalRep k 961=0 from arrow_incompatible k b 36 38 [50, 17, 21, 69, 8, 66, 24, 19, 53] (normal_endpoints 961) h]
    exact Submodule.zero_mem _
lemma extension_962_66 : a k 66*normalRep k 962=normalRep k 1060 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8] 66).symm
lemma extension_962_67 : a k 67*normalRep k 962=0 := by
  change a k 67*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_734 (a k) (relation_zero k) (e k 37)
lemma extension_962_68 : a k 68*normalRep k 962=normalRep k 1061 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8] 68).symm
lemma arrow_span_962 (b : Fin 75) : a k b*normalRep k 962 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_962_66 k]
      exact normal_mem k 1060
    · rw [extension_962_67 k]
      exact Submodule.zero_mem _
    · rw [extension_962_68 k]
      exact normal_mem k 1061
  · rw [show a k b*normalRep k 962=0 from arrow_incompatible k b 37 42 [52, 41, 43, 47, 7, 17, 21, 69, 8] (normal_endpoints 962) h]
    exact Submodule.zero_mem _
lemma extension_963_3 : a k 3*normalRep k 963=normalRep k 1061 := by
  change a k 3*walk k 37 [52, 41, 43, 47, 7, 17, 21, 70, 22]=walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 68]
  rw [← walk_snoc]
  exact Universal.mul_reduced_751 (a k) (relation_zero k) (e k 37)
lemma arrow_span_963 (b : Fin 75) : a k b*normalRep k 963 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_963_3 k]
      exact normal_mem k 1061
  · rw [show a k b*normalRep k 963=0 from arrow_incompatible k b 37 3 [52, 41, 43, 47, 7, 17, 21, 70, 22] (normal_endpoints 963) h]
    exact Submodule.zero_mem _
lemma extension_964_37 : a k 37*normalRep k 964=(-normalRep k 1060) := by
  change a k 37*walk k 37 [52, 41, 43, 48, 51, 64, 36, 71, 72]=(-walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66])
  rw [← walk_snoc]
  exact Universal.mul_reduced_801 (a k) (relation_zero k) (e k 37)
lemma extension_964_38 : a k 38*normalRep k 964=normalRep k 1062 := by
  exact (walk_snoc k 37 [52, 41, 43, 48, 51, 64, 36, 71, 72] 38).symm
lemma arrow_span_964 (b : Fin 75) : a k b*normalRep k 964 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_964_37 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1060)
    · rw [extension_964_38 k]
      exact normal_mem k 1062
  · rw [show a k b*normalRep k 964=0 from arrow_incompatible k b 37 29 [52, 41, 43, 48, 51, 64, 36, 71, 72] (normal_endpoints 964) h]
    exact Submodule.zero_mem _
lemma extension_965_0 : a k 0*normalRep k 965=normalRep k 1063 := by
  exact (walk_snoc k 37 [52, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_965 (b : Fin 75) : a k b*normalRep k 965 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_965_0 k]
      exact normal_mem k 1063
  · rw [show a k b*normalRep k 965=0 from arrow_incompatible k b 37 0 [52, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 965) h]
    exact Submodule.zero_mem _
lemma arrow_span_966 (b : Fin 75) : a k b*normalRep k 966 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 966=0 from arrow_incompatible k b 38 46 [54, 15, 1, 34, 63, 20, 30, 2, 0] (normal_endpoints 966) h]
    exact Submodule.zero_mem _
lemma extension_967_24 : a k 24*normalRep k 967=normalRep k 1064 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_967_25 : a k 25*normalRep k 967=normalRep k 1065 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_967 (b : Fin 75) : a k b*normalRep k 967 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_967_24 k]
      exact normal_mem k 1064
    · rw [extension_967_25 k]
      exact normal_mem k 1065
  · rw [show a k b*normalRep k 967=0 from arrow_incompatible k b 38 20 [55, 27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 967) h]
    exact Submodule.zero_mem _
lemma extension_968_39 : a k 39*normalRep k 968=0 := by
  change a k 39*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_720 (a k) (relation_zero k) (e k 38)
lemma extension_968_40 : a k 40*normalRep k 968=(-normalRep k 1065) := by
  change a k 40*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_795 (a k) (relation_zero k) (e k 38)
lemma arrow_span_968 (b : Fin 75) : a k b*normalRep k 968 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_968_39 k]
      exact Submodule.zero_mem _
    · rw [extension_968_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1065)
  · rw [show a k b*normalRep k 968=0 from arrow_incompatible k b 38 30 [55, 27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 968) h]
    exact Submodule.zero_mem _
lemma extension_969_28 : a k 28*normalRep k 969=normalRep k 1066 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_969_29 : a k 29*normalRep k 969=normalRep k 1064 := by
  change a k 29*walk k 38 [55, 27, 58, 33, 13, 49, 71, 72, 38]=walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_767 (a k) (relation_zero k) (e k 38)
lemma arrow_span_969 (b : Fin 75) : a k b*normalRep k 969 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_969_28 k]
      exact normal_mem k 1066
    · rw [extension_969_29 k]
      exact normal_mem k 1064
  · rw [show a k b*normalRep k 969=0 from arrow_incompatible k b 38 23 [55, 27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 969) h]
    exact Submodule.zero_mem _
lemma extension_970_9 : a k 9*normalRep k 970=normalRep k 1067 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_970 (b : Fin 75) : a k b*normalRep k 970 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_970_9 k]
      exact normal_mem k 1067
  · rw [show a k b*normalRep k 970=0 from arrow_incompatible k b 39 9 [58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 970) h]
    exact Submodule.zero_mem _
lemma extension_971_52 : a k 52*normalRep k 971=normalRep k 1067 := by
  change a k 52*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_744 (a k) (relation_zero k) (e k 39)
lemma extension_971_53 : a k 53*normalRep k 971=normalRep k 1068 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_971 (b : Fin 75) : a k b*normalRep k 971 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_971_52 k]
      exact normal_mem k 1067
    · rw [extension_971_53 k]
      exact normal_mem k 1068
  · rw [show a k b*normalRep k 971=0 from arrow_incompatible k b 39 37 [58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 971) h]
    exact Submodule.zero_mem _
lemma extension_972_4 : a k 4*normalRep k 972=normalRep k 1068 := by
  change a k 4*walk k 39 [58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_788 (a k) (relation_zero k) (e k 39)
lemma arrow_span_972 (b : Fin 75) : a k b*normalRep k 972 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_972_4 k]
      exact normal_mem k 1068
  · rw [show a k b*normalRep k 972=0 from arrow_incompatible k b 39 4 [58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 972) h]
    exact Submodule.zero_mem _
lemma extension_973_2 : a k 2*normalRep k 973=normalRep k 1069 := by
  exact (walk_snoc k 40 [60, 4, 54, 15, 1, 34, 63, 20, 30] 2).symm
lemma arrow_span_973 (b : Fin 75) : a k b*normalRep k 973 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_973_2 k]
      exact normal_mem k 1069
  · rw [show a k b*normalRep k 973=0 from arrow_incompatible k b 40 2 [60, 4, 54, 15, 1, 34, 63, 20, 30] (normal_endpoints 973) h]
    exact Submodule.zero_mem _
lemma extension_974_8 : a k 8*normalRep k 974=normalRep k 1070 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_974 (b : Fin 75) : a k b*normalRep k 974 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_974_8 k]
      exact normal_mem k 1070
  · rw [show a k b*normalRep k 974=0 from arrow_incompatible k b 40 8 [61, 35, 55, 27, 58, 33, 13, 49, 69] (normal_endpoints 974) h]
    exact Submodule.zero_mem _
lemma extension_975_72 : a k 72*normalRep k 975=normalRep k 1071 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 71] 72).symm
lemma extension_975_73 : a k 73*normalRep k 975=normalRep k 1070 := by
  change a k 73*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 71]=walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_798 (a k) (relation_zero k) (e k 40)
lemma arrow_span_975 (b : Fin 75) : a k b*normalRep k 975 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_975_72 k]
      exact normal_mem k 1071
    · rw [extension_975_73 k]
      exact normal_mem k 1070
  · rw [show a k b*normalRep k 975=0 from arrow_incompatible k b 40 44 [61, 35, 55, 27, 58, 33, 13, 49, 71] (normal_endpoints 975) h]
    exact Submodule.zero_mem _
lemma extension_976_22 : a k 22*normalRep k 976=normalRep k 1072 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 34, 63, 21, 70] 22).symm
lemma extension_976_23 : a k 23*normalRep k 976=normalRep k 1070 := by
  change a k 23*walk k 40 [61, 35, 55, 27, 58, 34, 63, 21, 70]=walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_799 (a k) (relation_zero k) (e k 40)
lemma arrow_span_976 (b : Fin 75) : a k b*normalRep k 976 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_976_22 k]
      exact normal_mem k 1072
    · rw [extension_976_23 k]
      exact normal_mem k 1070
  · rw [show a k b*normalRep k 976=0 from arrow_incompatible k b 40 19 [61, 35, 55, 27, 58, 34, 63, 21, 70] (normal_endpoints 976) h]
    exact Submodule.zero_mem _
lemma extension_977_43 : a k 43*normalRep k 977=0 := by
  change a k 43*walk k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_729 (a k) (relation_zero k) (e k 41)
lemma extension_977_44 : a k 44*normalRep k 977=normalRep k 1073 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_977 (b : Fin 75) : a k b*normalRep k 977 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_977_43 k]
      exact Submodule.zero_mem _
    · rw [extension_977_44 k]
      exact normal_mem k 1073
  · rw [show a k b*normalRep k 977=0 from arrow_incompatible k b 41 32 [63, 21, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 977) h]
    exact Submodule.zero_mem _
lemma extension_978_15 : a k 15*normalRep k 978=normalRep k 1074 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_978_16 : a k 16*normalRep k 978=normalRep k 1073 := by
  change a k 16*walk k 41 [63, 21, 69, 8, 66, 24, 19, 53, 54]=walk k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_782 (a k) (relation_zero k) (e k 41)
lemma arrow_span_978 (b : Fin 75) : a k b*normalRep k 978 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_978_15 k]
      exact normal_mem k 1074
    · rw [extension_978_16 k]
      exact normal_mem k 1073
  · rw [show a k b*normalRep k 978=0 from arrow_incompatible k b 41 15 [63, 21, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 978) h]
    exact Submodule.zero_mem _
lemma extension_979_20 : a k 20*normalRep k 979=normalRep k 1075 := by
  exact (walk_snoc k 42 [66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_979_21 : a k 21*normalRep k 979=0 := by
  change a k 21*walk k 42 [66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_792 (a k) (relation_zero k) (e k 42)
lemma arrow_span_979 (b : Fin 75) : a k b*normalRep k 979 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_979_20 k]
      exact normal_mem k 1075
    · rw [extension_979_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 979=0 from arrow_incompatible k b 42 18 [66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 979) h]
    exact Submodule.zero_mem _
lemma extension_980_49 : a k 49*normalRep k 980=normalRep k 1076 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13] 49).symm
lemma arrow_span_980 (b : Fin 75) : a k b*normalRep k 980 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_980_49 k]
      exact normal_mem k 1076
  · rw [show a k b*normalRep k 980=0 from arrow_incompatible k b 42 35 [67, 32, 61, 35, 55, 27, 58, 33, 13] (normal_endpoints 980) h]
    exact Submodule.zero_mem _
lemma extension_981_20 : a k 20*normalRep k 981=0 := by
  change a k 20*walk k 42 [67, 32, 61, 35, 55, 27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_741 (a k) (relation_zero k) (e k 42)
lemma extension_981_21 : a k 21*normalRep k 981=normalRep k 1077 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 34, 63] 21).symm
lemma arrow_span_981 (b : Fin 75) : a k b*normalRep k 981 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_981_20 k]
      exact Submodule.zero_mem _
    · rw [extension_981_21 k]
      exact normal_mem k 1077
  · rw [show a k b*normalRep k 981=0 from arrow_incompatible k b 42 18 [67, 32, 61, 35, 55, 27, 58, 34, 63] (normal_endpoints 981) h]
    exact Submodule.zero_mem _
lemma extension_982_36 : a k 36*normalRep k 982=normalRep k 1077 + normalRep k 1076 := by
  change a k 36*walk k 42 [67, 32, 61, 35, 55, 27, 58, 34, 64]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_793 (a k) (relation_zero k) (e k 42)
lemma arrow_span_982 (b : Fin 75) : a k b*normalRep k 982 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_982_36 k]
      exact (normalSpan k).add_mem (normal_mem k 1077) (normal_mem k 1076)
  · rw [show a k b*normalRep k 982=0 from arrow_incompatible k b 42 28 [67, 32, 61, 35, 55, 27, 58, 34, 64] (normal_endpoints 982) h]
    exact Submodule.zero_mem _
lemma extension_983_5 : a k 5*normalRep k 983=normalRep k 1078 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_983 (b : Fin 75) : a k b*normalRep k 983 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_983_5 k]
      exact normal_mem k 1078
  · rw [show a k b*normalRep k 983=0 from arrow_incompatible k b 43 5 [69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 983) h]
    exact Submodule.zero_mem _
lemma extension_984_33 : a k 33*normalRep k 984=0 := by
  change a k 33*walk k 43 [69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_714 (a k) (relation_zero k) (e k 43)
lemma extension_984_34 : a k 34*normalRep k 984=normalRep k 1078 := by
  change a k 34*walk k 43 [69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 43 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_784 (a k) (relation_zero k) (e k 43)
lemma arrow_span_984 (b : Fin 75) : a k b*normalRep k 984 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_984_33 k]
      exact Submodule.zero_mem _
    · rw [extension_984_34 k]
      exact normal_mem k 1078
  · rw [show a k b*normalRep k 984=0 from arrow_incompatible k b 43 26 [69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 984) h]
    exact Submodule.zero_mem _
lemma extension_985_33 : a k 33*normalRep k 985=0 := by
  change a k 33*walk k 43 [70, 22, 3, 40, 60, 4, 54, 15, 1]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_715 (a k) (relation_zero k) (e k 43)
lemma extension_985_34 : a k 34*normalRep k 985=normalRep k 1079 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 60, 4, 54, 15, 1] 34).symm
lemma arrow_span_985 (b : Fin 75) : a k b*normalRep k 985 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_985_33 k]
      exact Submodule.zero_mem _
    · rw [extension_985_34 k]
      exact normal_mem k 1079
  · rw [show a k b*normalRep k 985=0 from arrow_incompatible k b 43 26 [70, 22, 3, 40, 60, 4, 54, 15, 1] (normal_endpoints 985) h]
    exact Submodule.zero_mem _
lemma extension_986_5 : a k 5*normalRep k 986=normalRep k 1079 := by
  change a k 5*walk k 43 [70, 22, 3, 40, 60, 4, 54, 16, 57]=walk k 43 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_785 (a k) (relation_zero k) (e k 43)
lemma arrow_span_986 (b : Fin 75) : a k b*normalRep k 986 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_986_5 k]
      exact normal_mem k 1079
  · rw [show a k b*normalRep k 986=0 from arrow_incompatible k b 43 5 [70, 22, 3, 40, 60, 4, 54, 16, 57] (normal_endpoints 986) h]
    exact Submodule.zero_mem _
lemma extension_987_63 : a k 63*normalRep k 987=normalRep k 1080 := by
  exact (walk_snoc k 44 [72, 37, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_987_64 : a k 64*normalRep k 987=0 := by
  change a k 64*walk k 44 [72, 37, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_718 (a k) (relation_zero k) (e k 44)
lemma extension_987_65 : a k 65*normalRep k 987=0 := by
  change a k 65*walk k 44 [72, 37, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_732 (a k) (relation_zero k) (e k 44)
lemma arrow_span_987 (b : Fin 75) : a k b*normalRep k 987 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_987_63 k]
      exact normal_mem k 1080
    · rw [extension_987_64 k]
      exact Submodule.zero_mem _
    · rw [extension_987_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 987=0 from arrow_incompatible k b 44 41 [72, 37, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 987) h]
    exact Submodule.zero_mem _
lemma extension_988_13 : a k 13*normalRep k 988=normalRep k 1081 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33] 13).symm
lemma arrow_span_988 (b : Fin 75) : a k b*normalRep k 988 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_988_13 k]
      exact normal_mem k 1081
  · rw [show a k b*normalRep k 988=0 from arrow_incompatible k b 44 13 [73, 67, 32, 61, 35, 55, 27, 58, 33] (normal_endpoints 988) h]
    exact Submodule.zero_mem _
lemma extension_989_63 : a k 63*normalRep k 989=normalRep k 1082 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34] 63).symm
lemma extension_989_64 : a k 64*normalRep k 989=normalRep k 1083 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34] 64).symm
lemma extension_989_65 : a k 65*normalRep k 989=normalRep k 1081 := by
  change a k 65*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_762 (a k) (relation_zero k) (e k 44)
lemma arrow_span_989 (b : Fin 75) : a k b*normalRep k 989 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_989_63 k]
      exact normal_mem k 1082
    · rw [extension_989_64 k]
      exact normal_mem k 1083
    · rw [extension_989_65 k]
      exact normal_mem k 1081
  · rw [show a k b*normalRep k 989=0 from arrow_incompatible k b 44 41 [73, 67, 32, 61, 35, 55, 27, 58, 34] (normal_endpoints 989) h]
    exact Submodule.zero_mem _
lemma extension_990_17 : a k 17*normalRep k 990=normalRep k 1082 := by
  change a k 17*walk k 44 [73, 67, 32, 61, 35, 55, 27, 59, 50]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_774 (a k) (relation_zero k) (e k 44)
lemma arrow_span_990 (b : Fin 75) : a k b*normalRep k 990 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_990_17 k]
      exact normal_mem k 1082
  · rw [show a k b*normalRep k 990=0 from arrow_incompatible k b 44 16 [73, 67, 32, 61, 35, 55, 27, 59, 50] (normal_endpoints 990) h]
    exact Submodule.zero_mem _
lemma extension_991_35 : a k 35*normalRep k 991=normalRep k 1084 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61] 35).symm
lemma arrow_span_991 (b : Fin 75) : a k b*normalRep k 991 ∈ normalSpan k := by
  by_cases h : arrowSource b=27
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [35] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_991_35 k]
      exact normal_mem k 1084
  · rw [show a k b*normalRep k 991=0 from arrow_incompatible k b 45 27 [74, 10, 11, 26, 31, 73, 67, 32, 61] (normal_endpoints 991) h]
    exact Submodule.zero_mem _
lemma extension_992_52 : a k 52*normalRep k 992=normalRep k 1085 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 62] 52).symm
lemma extension_992_53 : a k 53*normalRep k 992=normalRep k 1084 := by
  change a k 53*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 62]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35]
  rw [← walk_snoc]
  exact Universal.mul_reduced_789 (a k) (relation_zero k) (e k 45)
lemma arrow_span_992 (b : Fin 75) : a k b*normalRep k 992 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_992_52 k]
      exact normal_mem k 1085
    · rw [extension_992_53 k]
      exact normal_mem k 1084
  · rw [show a k b*normalRep k 992=0 from arrow_incompatible k b 45 37 [74, 10, 11, 26, 31, 73, 67, 32, 62] (normal_endpoints 992) h]
    exact Submodule.zero_mem _
lemma extension_993_30 : a k 30*normalRep k 993=normalRep k 1086 := by
  exact (walk_snoc k 3 [3, 40, 60, 4, 54, 15, 1, 34, 63, 20] 30).symm
lemma extension_993_31 : a k 31*normalRep k 993=0 := by
  change a k 31*walk k 3 [3, 40, 60, 4, 54, 15, 1, 34, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_832 (a k) (relation_zero k) (e k 3)
lemma arrow_span_993 (b : Fin 75) : a k b*normalRep k 993 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_993_30 k]
      exact normal_mem k 1086
    · rw [extension_993_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 993=0 from arrow_incompatible k b 3 24 [3, 40, 60, 4, 54, 15, 1, 34, 63, 20] (normal_endpoints 993) h]
    exact Submodule.zero_mem _
lemma arrow_span_994 (b : Fin 75) : a k b*normalRep k 994 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 994=0 from arrow_incompatible k b 4 46 [4, 54, 15, 1, 34, 63, 20, 30, 2, 0] (normal_endpoints 994) h]
    exact Submodule.zero_mem _
lemma extension_995_41 : a k 41*normalRep k 995=normalRep k 1087 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_995_42 : a k 42*normalRep k 995=0 := by
  change a k 42*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_809 (a k) (relation_zero k) (e k 6)
lemma arrow_span_995 (b : Fin 75) : a k b*normalRep k 995 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_995_41 k]
      exact normal_mem k 1087
    · rw [extension_995_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 995=0 from arrow_incompatible k b 6 31 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9] (normal_endpoints 995) h]
    exact Submodule.zero_mem _
lemma extension_996_54 : a k 54*normalRep k 996=normalRep k 1088 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_996_55 : a k 55*normalRep k 996=0 := by
  change a k 55*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_812 (a k) (relation_zero k) (e k 6)
lemma extension_996_56 : a k 56*normalRep k 996=normalRep k 1087 := by
  change a k 56*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 19, 53]=walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_856 (a k) (relation_zero k) (e k 6)
lemma arrow_span_996 (b : Fin 75) : a k b*normalRep k 996 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_996_54 k]
      exact normal_mem k 1088
    · rw [extension_996_55 k]
      exact Submodule.zero_mem _
    · rw [extension_996_56 k]
      exact normal_mem k 1087
  · rw [show a k b*normalRep k 996=0 from arrow_incompatible k b 6 38 [6, 7, 17, 21, 69, 8, 66, 24, 19, 53] (normal_endpoints 996) h]
    exact Submodule.zero_mem _
lemma extension_997_43 : a k 43*normalRep k 997=0 := by
  change a k 43*walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_815 (a k) (relation_zero k) (e k 7)
lemma extension_997_44 : a k 44*normalRep k 997=normalRep k 1089 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_997 (b : Fin 75) : a k b*normalRep k 997 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_997_43 k]
      exact Submodule.zero_mem _
    · rw [extension_997_44 k]
      exact normal_mem k 1089
  · rw [show a k b*normalRep k 997=0 from arrow_incompatible k b 7 32 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 997) h]
    exact Submodule.zero_mem _
lemma extension_998_15 : a k 15*normalRep k 998=normalRep k 1090 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_998_16 : a k 16*normalRep k 998=normalRep k 1089 := by
  change a k 16*walk k 7 [7, 17, 21, 69, 8, 66, 24, 19, 53, 54]=walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_860 (a k) (relation_zero k) (e k 7)
lemma arrow_span_998 (b : Fin 75) : a k b*normalRep k 998 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_998_15 k]
      exact normal_mem k 1090
    · rw [extension_998_16 k]
      exact normal_mem k 1089
  · rw [show a k b*normalRep k 998=0 from arrow_incompatible k b 7 15 [7, 17, 21, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 998) h]
    exact Submodule.zero_mem _
lemma extension_999_20 : a k 20*normalRep k 999=normalRep k 1091 := by
  exact (walk_snoc k 8 [8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_999_21 : a k 21*normalRep k 999=0 := by
  change a k 21*walk k 8 [8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_871 (a k) (relation_zero k) (e k 8)
lemma arrow_span_999 (b : Fin 75) : a k b*normalRep k 999 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_999_20 k]
      exact normal_mem k 1091
    · rw [extension_999_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 999=0 from arrow_incompatible k b 8 18 [8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 999) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
