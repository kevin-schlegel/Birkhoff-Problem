import N6NormalData
import N6Reduced0
import N6Reduced1
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_100_54 : a k 54*normalRep k 100=normalRep k 191 := by
  exact (walk_snoc k 37 [53] 54).symm
lemma extension_100_55 : a k 55*normalRep k 100=normalRep k 192 := by
  exact (walk_snoc k 37 [53] 55).symm
lemma extension_100_56 : a k 56*normalRep k 100=normalRep k 189 := by
  change a k 56*walk k 37 [53]=walk k 37 [52, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_33 (a k) (relation_zero k) (e k 37)
lemma arrow_span_100 (b : Fin 75) : a k b*normalRep k 100 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_100_54 k]
      exact normal_mem k 191
    · rw [extension_100_55 k]
      exact normal_mem k 192
    · rw [extension_100_56 k]
      exact normal_mem k 189
  · rw [show a k b*normalRep k 100=0 from arrow_incompatible k b 37 38 [53] (normal_endpoints 100) h]
    exact Submodule.zero_mem _
lemma extension_101_15 : a k 15*normalRep k 101=normalRep k 193 := by
  exact (walk_snoc k 38 [54] 15).symm
lemma extension_101_16 : a k 16*normalRep k 101=normalRep k 194 := by
  exact (walk_snoc k 38 [54] 16).symm
lemma arrow_span_101 (b : Fin 75) : a k b*normalRep k 101 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_101_15 k]
      exact normal_mem k 193
    · rw [extension_101_16 k]
      exact normal_mem k 194
  · rw [show a k b*normalRep k 101=0 from arrow_incompatible k b 38 15 [54] (normal_endpoints 101) h]
    exact Submodule.zero_mem _
lemma extension_102_27 : a k 27*normalRep k 102=normalRep k 195 := by
  exact (walk_snoc k 38 [55] 27).symm
lemma arrow_span_102 (b : Fin 75) : a k b*normalRep k 102 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_102_27 k]
      exact normal_mem k 195
  · rw [show a k b*normalRep k 102=0 from arrow_incompatible k b 38 22 [55] (normal_endpoints 102) h]
    exact Submodule.zero_mem _
lemma extension_103_43 : a k 43*normalRep k 103=normalRep k 196 := by
  exact (walk_snoc k 38 [56] 43).symm
lemma extension_103_44 : a k 44*normalRep k 103=normalRep k 194 + normalRep k 195 := by
  change a k 44*walk k 38 [56]=walk k 38 [54, 16] + walk k 38 [55, 27]
  rw [← walk_snoc]
  exact Universal.mul_reduced_34 (a k) (relation_zero k) (e k 38)
lemma arrow_span_103 (b : Fin 75) : a k b*normalRep k 103 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_103_43 k]
      exact normal_mem k 196
    · rw [extension_103_44 k]
      exact (normalSpan k).add_mem (normal_mem k 194) (normal_mem k 195)
  · rw [show a k b*normalRep k 103=0 from arrow_incompatible k b 38 32 [56] (normal_endpoints 103) h]
    exact Submodule.zero_mem _
lemma extension_104_5 : a k 5*normalRep k 104=normalRep k 197 := by
  exact (walk_snoc k 39 [57] 5).symm
lemma arrow_span_104 (b : Fin 75) : a k b*normalRep k 104 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_104_5 k]
      exact normal_mem k 197
  · rw [show a k b*normalRep k 104=0 from arrow_incompatible k b 39 5 [57] (normal_endpoints 104) h]
    exact Submodule.zero_mem _
lemma extension_105_33 : a k 33*normalRep k 105=normalRep k 198 := by
  exact (walk_snoc k 39 [58] 33).symm
lemma extension_105_34 : a k 34*normalRep k 105=normalRep k 199 := by
  exact (walk_snoc k 39 [58] 34).symm
lemma arrow_span_105 (b : Fin 75) : a k b*normalRep k 105 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_105_33 k]
      exact normal_mem k 198
    · rw [extension_105_34 k]
      exact normal_mem k 199
  · rw [show a k b*normalRep k 105=0 from arrow_incompatible k b 39 26 [58] (normal_endpoints 105) h]
    exact Submodule.zero_mem _
lemma extension_106_50 : a k 50*normalRep k 106=normalRep k 200 := by
  exact (walk_snoc k 39 [59] 50).symm
lemma extension_106_51 : a k 51*normalRep k 106=(-normalRep k 197) + normalRep k 199 := by
  change a k 51*walk k 39 [59]=(-walk k 39 [57, 5]) + walk k 39 [58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_35 (a k) (relation_zero k) (e k 39)
lemma arrow_span_106 (b : Fin 75) : a k b*normalRep k 106 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_106_50 k]
      exact normal_mem k 200
    · rw [extension_106_51 k]
      exact (normalSpan k).add_mem ((normalSpan k).smul_mem (-1:k) (normal_mem k 197)) (normal_mem k 199)
  · rw [show a k b*normalRep k 106=0 from arrow_incompatible k b 39 36 [59] (normal_endpoints 106) h]
    exact Submodule.zero_mem _
lemma extension_107_4 : a k 4*normalRep k 107=normalRep k 201 := by
  exact (walk_snoc k 40 [60] 4).symm
lemma arrow_span_107 (b : Fin 75) : a k b*normalRep k 107 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_107_4 k]
      exact normal_mem k 201
  · rw [show a k b*normalRep k 107=0 from arrow_incompatible k b 40 4 [60] (normal_endpoints 107) h]
    exact Submodule.zero_mem _
lemma extension_108_35 : a k 35*normalRep k 108=normalRep k 202 := by
  exact (walk_snoc k 40 [61] 35).symm
lemma arrow_span_108 (b : Fin 75) : a k b*normalRep k 108 ∈ normalSpan k := by
  by_cases h : arrowSource b=27
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [35] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_108_35 k]
      exact normal_mem k 202
  · rw [show a k b*normalRep k 108=0 from arrow_incompatible k b 40 27 [61] (normal_endpoints 108) h]
    exact Submodule.zero_mem _
lemma extension_109_52 : a k 52*normalRep k 109=normalRep k 203 := by
  exact (walk_snoc k 40 [62] 52).symm
lemma extension_109_53 : a k 53*normalRep k 109=normalRep k 201 + normalRep k 202 := by
  change a k 53*walk k 40 [62]=walk k 40 [60, 4] + walk k 40 [61, 35]
  rw [← walk_snoc]
  exact Universal.mul_reduced_36 (a k) (relation_zero k) (e k 40)
lemma arrow_span_109 (b : Fin 75) : a k b*normalRep k 109 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_109_52 k]
      exact normal_mem k 203
    · rw [extension_109_53 k]
      exact (normalSpan k).add_mem (normal_mem k 201) (normal_mem k 202)
  · rw [show a k b*normalRep k 109=0 from arrow_incompatible k b 40 37 [62] (normal_endpoints 109) h]
    exact Submodule.zero_mem _
lemma extension_110_20 : a k 20*normalRep k 110=normalRep k 204 := by
  exact (walk_snoc k 41 [63] 20).symm
lemma extension_110_21 : a k 21*normalRep k 110=normalRep k 205 := by
  exact (walk_snoc k 41 [63] 21).symm
lemma arrow_span_110 (b : Fin 75) : a k b*normalRep k 110 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_110_20 k]
      exact normal_mem k 204
    · rw [extension_110_21 k]
      exact normal_mem k 205
  · rw [show a k b*normalRep k 110=0 from arrow_incompatible k b 41 18 [63] (normal_endpoints 110) h]
    exact Submodule.zero_mem _
lemma extension_111_36 : a k 36*normalRep k 111=normalRep k 206 := by
  exact (walk_snoc k 41 [64] 36).symm
lemma arrow_span_111 (b : Fin 75) : a k b*normalRep k 111 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_111_36 k]
      exact normal_mem k 206
  · rw [show a k b*normalRep k 111=0 from arrow_incompatible k b 41 28 [64] (normal_endpoints 111) h]
    exact Submodule.zero_mem _
lemma extension_112_49 : a k 49*normalRep k 112=(-normalRep k 205) + normalRep k 206 := by
  change a k 49*walk k 41 [65]=(-walk k 41 [63, 21]) + walk k 41 [64, 36]
  rw [← walk_snoc]
  exact Universal.mul_reduced_37 (a k) (relation_zero k) (e k 41)
lemma arrow_span_112 (b : Fin 75) : a k b*normalRep k 112 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_112_49 k]
      exact (normalSpan k).add_mem ((normalSpan k).smul_mem (-1:k) (normal_mem k 205)) (normal_mem k 206)
  · rw [show a k b*normalRep k 112=0 from arrow_incompatible k b 41 35 [65] (normal_endpoints 112) h]
    exact Submodule.zero_mem _
lemma extension_113_24 : a k 24*normalRep k 113=normalRep k 207 := by
  exact (walk_snoc k 42 [66] 24).symm
lemma extension_113_25 : a k 25*normalRep k 113=normalRep k 208 := by
  exact (walk_snoc k 42 [66] 25).symm
lemma arrow_span_113 (b : Fin 75) : a k b*normalRep k 113 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_113_24 k]
      exact normal_mem k 207
    · rw [extension_113_25 k]
      exact normal_mem k 208
  · rw [show a k b*normalRep k 113=0 from arrow_incompatible k b 42 20 [66] (normal_endpoints 113) h]
    exact Submodule.zero_mem _
lemma extension_114_32 : a k 32*normalRep k 114=normalRep k 209 := by
  exact (walk_snoc k 42 [67] 32).symm
lemma arrow_span_114 (b : Fin 75) : a k b*normalRep k 114 ∈ normalSpan k := by
  by_cases h : arrowSource b=25
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [32] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_114_32 k]
      exact normal_mem k 209
  · rw [show a k b*normalRep k 114=0 from arrow_incompatible k b 42 25 [67] (normal_endpoints 114) h]
    exact Submodule.zero_mem _
lemma extension_115_39 : a k 39*normalRep k 115=normalRep k 210 := by
  exact (walk_snoc k 42 [68] 39).symm
lemma extension_115_40 : a k 40*normalRep k 115=(-normalRep k 208) + normalRep k 209 := by
  change a k 40*walk k 42 [68]=(-walk k 42 [66, 25]) + walk k 42 [67, 32]
  rw [← walk_snoc]
  exact Universal.mul_reduced_38 (a k) (relation_zero k) (e k 42)
lemma arrow_span_115 (b : Fin 75) : a k b*normalRep k 115 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_115_39 k]
      exact normal_mem k 210
    · rw [extension_115_40 k]
      exact (normalSpan k).add_mem ((normalSpan k).smul_mem (-1:k) (normal_mem k 208)) (normal_mem k 209)
  · rw [show a k b*normalRep k 115=0 from arrow_incompatible k b 42 30 [68] (normal_endpoints 115) h]
    exact Submodule.zero_mem _
lemma extension_116_8 : a k 8*normalRep k 116=normalRep k 211 := by
  exact (walk_snoc k 43 [69] 8).symm
lemma arrow_span_116 (b : Fin 75) : a k b*normalRep k 116 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_116_8 k]
      exact normal_mem k 211
  · rw [show a k b*normalRep k 116=0 from arrow_incompatible k b 43 8 [69] (normal_endpoints 116) h]
    exact Submodule.zero_mem _
lemma extension_117_22 : a k 22*normalRep k 117=normalRep k 212 := by
  exact (walk_snoc k 43 [70] 22).symm
lemma extension_117_23 : a k 23*normalRep k 117=normalRep k 213 := by
  exact (walk_snoc k 43 [70] 23).symm
lemma arrow_span_117 (b : Fin 75) : a k b*normalRep k 117 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_117_22 k]
      exact normal_mem k 212
    · rw [extension_117_23 k]
      exact normal_mem k 213
  · rw [show a k b*normalRep k 117=0 from arrow_incompatible k b 43 19 [70] (normal_endpoints 117) h]
    exact Submodule.zero_mem _
lemma extension_118_72 : a k 72*normalRep k 118=normalRep k 214 := by
  exact (walk_snoc k 43 [71] 72).symm
lemma extension_118_73 : a k 73*normalRep k 118=normalRep k 211 + normalRep k 213 := by
  change a k 73*walk k 43 [71]=walk k 43 [69, 8] + walk k 43 [70, 23]
  rw [← walk_snoc]
  exact Universal.mul_reduced_39 (a k) (relation_zero k) (e k 43)
lemma arrow_span_118 (b : Fin 75) : a k b*normalRep k 118 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_118_72 k]
      exact normal_mem k 214
    · rw [extension_118_73 k]
      exact (normalSpan k).add_mem (normal_mem k 211) (normal_mem k 213)
  · rw [show a k b*normalRep k 118=0 from arrow_incompatible k b 43 44 [71] (normal_endpoints 118) h]
    exact Submodule.zero_mem _
lemma extension_119_37 : a k 37*normalRep k 119=normalRep k 215 := by
  exact (walk_snoc k 44 [72] 37).symm
lemma extension_119_38 : a k 38*normalRep k 119=normalRep k 216 := by
  exact (walk_snoc k 44 [72] 38).symm
lemma arrow_span_119 (b : Fin 75) : a k b*normalRep k 119 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_119_37 k]
      exact normal_mem k 215
    · rw [extension_119_38 k]
      exact normal_mem k 216
  · rw [show a k b*normalRep k 119=0 from arrow_incompatible k b 44 29 [72] (normal_endpoints 119) h]
    exact Submodule.zero_mem _
lemma extension_120_66 : a k 66*normalRep k 120=normalRep k 215 := by
  change a k 66*walk k 44 [73]=walk k 44 [72, 37]
  rw [← walk_snoc]
  exact Universal.mul_reduced_40 (a k) (relation_zero k) (e k 44)
lemma extension_120_67 : a k 67*normalRep k 120=normalRep k 217 := by
  exact (walk_snoc k 44 [73] 67).symm
lemma extension_120_68 : a k 68*normalRep k 120=normalRep k 218 := by
  exact (walk_snoc k 44 [73] 68).symm
lemma arrow_span_120 (b : Fin 75) : a k b*normalRep k 120 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_120_66 k]
      exact normal_mem k 215
    · rw [extension_120_67 k]
      exact normal_mem k 217
    · rw [extension_120_68 k]
      exact normal_mem k 218
  · rw [show a k b*normalRep k 120=0 from arrow_incompatible k b 44 42 [73] (normal_endpoints 120) h]
    exact Submodule.zero_mem _
lemma extension_121_10 : a k 10*normalRep k 121=normalRep k 219 := by
  exact (walk_snoc k 45 [74] 10).symm
lemma arrow_span_121 (b : Fin 75) : a k b*normalRep k 121 ∈ normalSpan k := by
  by_cases h : arrowSource b=10
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [10] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_121_10 k]
      exact normal_mem k 219
  · rw [show a k b*normalRep k 121=0 from arrow_incompatible k b 45 10 [74] (normal_endpoints 121) h]
    exact Submodule.zero_mem _
lemma extension_122_63 : a k 63*normalRep k 122=normalRep k 220 := by
  exact (walk_snoc k 1 [1, 34] 63).symm
lemma extension_122_64 : a k 64*normalRep k 122=0 := by
  change a k 64*walk k 1 [1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_42 (a k) (relation_zero k) (e k 1)
lemma extension_122_65 : a k 65*normalRep k 122=0 := by
  change a k 65*walk k 1 [1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_73 (a k) (relation_zero k) (e k 1)
lemma arrow_span_122 (b : Fin 75) : a k b*normalRep k 122 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_122_63 k]
      exact normal_mem k 220
    · rw [extension_122_64 k]
      exact Submodule.zero_mem _
    · rw [extension_122_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 122=0 from arrow_incompatible k b 1 41 [1, 34] (normal_endpoints 122) h]
    exact Submodule.zero_mem _
lemma arrow_span_123 (b : Fin 75) : a k b*normalRep k 123 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 123=0 from arrow_incompatible k b 2 46 [2, 0] (normal_endpoints 123) h]
    exact Submodule.zero_mem _
lemma extension_124_60 : a k 60*normalRep k 124=normalRep k 221 := by
  exact (walk_snoc k 3 [3, 40] 60).symm
lemma extension_124_61 : a k 61*normalRep k 124=0 := by
  change a k 61*walk k 3 [3, 40]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_79 (a k) (relation_zero k) (e k 3)
lemma extension_124_62 : a k 62*normalRep k 124=normalRep k 222 := by
  exact (walk_snoc k 3 [3, 40] 62).symm
lemma arrow_span_124 (b : Fin 75) : a k b*normalRep k 124 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_124_60 k]
      exact normal_mem k 221
    · rw [extension_124_61 k]
      exact Submodule.zero_mem _
    · rw [extension_124_62 k]
      exact normal_mem k 222
  · rw [show a k b*normalRep k 124=0 from arrow_incompatible k b 3 40 [3, 40] (normal_endpoints 124) h]
    exact Submodule.zero_mem _
lemma extension_125_15 : a k 15*normalRep k 125=normalRep k 223 := by
  exact (walk_snoc k 4 [4, 54] 15).symm
lemma extension_125_16 : a k 16*normalRep k 125=normalRep k 224 := by
  exact (walk_snoc k 4 [4, 54] 16).symm
lemma arrow_span_125 (b : Fin 75) : a k b*normalRep k 125 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_125_15 k]
      exact normal_mem k 223
    · rw [extension_125_16 k]
      exact normal_mem k 224
  · rw [show a k b*normalRep k 125=0 from arrow_incompatible k b 4 15 [4, 54] (normal_endpoints 125) h]
    exact Submodule.zero_mem _
lemma extension_126_43 : a k 43*normalRep k 126=0 := by
  change a k 43*walk k 4 [4, 56]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_45 (a k) (relation_zero k) (e k 4)
lemma extension_126_44 : a k 44*normalRep k 126=normalRep k 224 := by
  change a k 44*walk k 4 [4, 56]=walk k 4 [4, 54, 16]
  rw [← walk_snoc]
  exact Universal.mul_reduced_94 (a k) (relation_zero k) (e k 4)
lemma arrow_span_126 (b : Fin 75) : a k b*normalRep k 126 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_126_43 k]
      exact Submodule.zero_mem _
    · rw [extension_126_44 k]
      exact normal_mem k 224
  · rw [show a k b*normalRep k 126=0 from arrow_incompatible k b 4 32 [4, 56] (normal_endpoints 126) h]
    exact Submodule.zero_mem _
lemma extension_127_20 : a k 20*normalRep k 127=normalRep k 225 := by
  exact (walk_snoc k 5 [5, 63] 20).symm
lemma extension_127_21 : a k 21*normalRep k 127=0 := by
  change a k 21*walk k 5 [5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_103 (a k) (relation_zero k) (e k 5)
lemma arrow_span_127 (b : Fin 75) : a k b*normalRep k 127 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_127_20 k]
      exact normal_mem k 225
    · rw [extension_127_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 127=0 from arrow_incompatible k b 5 18 [5, 63] (normal_endpoints 127) h]
    exact Submodule.zero_mem _
lemma extension_128_17 : a k 17*normalRep k 128=normalRep k 226 := by
  exact (walk_snoc k 6 [6, 7] 17).symm
lemma arrow_span_128 (b : Fin 75) : a k b*normalRep k 128 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_128_17 k]
      exact normal_mem k 226
  · rw [show a k b*normalRep k 128=0 from arrow_incompatible k b 6 16 [6, 7] (normal_endpoints 128) h]
    exact Submodule.zero_mem _
lemma extension_129_20 : a k 20*normalRep k 129=0 := by
  change a k 20*walk k 7 [7, 17]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_54 (a k) (relation_zero k) (e k 7)
lemma extension_129_21 : a k 21*normalRep k 129=normalRep k 227 := by
  exact (walk_snoc k 7 [7, 17] 21).symm
lemma arrow_span_129 (b : Fin 75) : a k b*normalRep k 129 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_129_20 k]
      exact Submodule.zero_mem _
    · rw [extension_129_21 k]
      exact normal_mem k 227
  · rw [show a k b*normalRep k 129=0 from arrow_incompatible k b 7 18 [7, 17] (normal_endpoints 129) h]
    exact Submodule.zero_mem _
lemma extension_130_24 : a k 24*normalRep k 130=normalRep k 228 := by
  exact (walk_snoc k 8 [8, 66] 24).symm
lemma extension_130_25 : a k 25*normalRep k 130=normalRep k 229 := by
  exact (walk_snoc k 8 [8, 66] 25).symm
lemma arrow_span_130 (b : Fin 75) : a k b*normalRep k 130 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_130_24 k]
      exact normal_mem k 228
    · rw [extension_130_25 k]
      exact normal_mem k 229
  · rw [show a k b*normalRep k 130=0 from arrow_incompatible k b 8 20 [8, 66] (normal_endpoints 130) h]
    exact Submodule.zero_mem _
lemma extension_131_39 : a k 39*normalRep k 131=0 := by
  change a k 39*walk k 8 [8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_48 (a k) (relation_zero k) (e k 8)
lemma extension_131_40 : a k 40*normalRep k 131=(-normalRep k 229) := by
  change a k 40*walk k 8 [8, 68]=(-walk k 8 [8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_106 (a k) (relation_zero k) (e k 8)
lemma arrow_span_131 (b : Fin 75) : a k b*normalRep k 131 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_131_39 k]
      exact Submodule.zero_mem _
    · rw [extension_131_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 229)
  · rw [show a k b*normalRep k 131=0 from arrow_incompatible k b 8 30 [8, 68] (normal_endpoints 131) h]
    exact Submodule.zero_mem _
lemma extension_132_43 : a k 43*normalRep k 132=0 := by
  change a k 43*walk k 9 [9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_81 (a k) (relation_zero k) (e k 9)
lemma extension_132_44 : a k 44*normalRep k 132=normalRep k 230 := by
  exact (walk_snoc k 9 [9, 41] 44).symm
lemma arrow_span_132 (b : Fin 75) : a k b*normalRep k 132 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_132_43 k]
      exact Submodule.zero_mem _
    · rw [extension_132_44 k]
      exact normal_mem k 230
  · rw [show a k b*normalRep k 132=0 from arrow_incompatible k b 9 32 [9, 41] (normal_endpoints 132) h]
    exact Submodule.zero_mem _
lemma extension_133_26 : a k 26*normalRep k 133=normalRep k 231 := by
  exact (walk_snoc k 10 [10, 11] 26).symm
lemma arrow_span_133 (b : Fin 75) : a k b*normalRep k 133 ∈ normalSpan k := by
  by_cases h : arrowSource b=21
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [26] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_133_26 k]
      exact normal_mem k 231
  · rw [show a k b*normalRep k 133=0 from arrow_incompatible k b 10 21 [10, 11] (normal_endpoints 133) h]
    exact Submodule.zero_mem _
lemma extension_134_30 : a k 30*normalRep k 134=0 := by
  change a k 30*walk k 11 [11, 26]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_68 (a k) (relation_zero k) (e k 11)
lemma extension_134_31 : a k 31*normalRep k 134=normalRep k 232 := by
  exact (walk_snoc k 11 [11, 26] 31).symm
lemma arrow_span_134 (b : Fin 75) : a k b*normalRep k 134 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_134_30 k]
      exact Submodule.zero_mem _
    · rw [extension_134_31 k]
      exact normal_mem k 232
  · rw [show a k b*normalRep k 134=0 from arrow_incompatible k b 11 24 [11, 26] (normal_endpoints 134) h]
    exact Submodule.zero_mem _
lemma extension_135_54 : a k 54*normalRep k 135=0 := by
  change a k 54*walk k 12 [12, 35]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_75 (a k) (relation_zero k) (e k 12)
lemma extension_135_55 : a k 55*normalRep k 135=normalRep k 233 := by
  exact (walk_snoc k 12 [12, 35] 55).symm
lemma extension_135_56 : a k 56*normalRep k 135=normalRep k 234 := by
  exact (walk_snoc k 12 [12, 35] 56).symm
lemma arrow_span_135 (b : Fin 75) : a k b*normalRep k 135 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_135_54 k]
      exact Submodule.zero_mem _
    · rw [extension_135_55 k]
      exact normal_mem k 233
    · rw [extension_135_56 k]
      exact normal_mem k 234
  · rw [show a k b*normalRep k 135=0 from arrow_incompatible k b 12 38 [12, 35] (normal_endpoints 135) h]
    exact Submodule.zero_mem _
lemma extension_136_69 : a k 69*normalRep k 136=normalRep k 235 := by
  exact (walk_snoc k 13 [13, 49] 69).symm
lemma extension_136_70 : a k 70*normalRep k 136=0 := by
  change a k 70*walk k 13 [13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_88 (a k) (relation_zero k) (e k 13)
lemma extension_136_71 : a k 71*normalRep k 136=normalRep k 236 := by
  exact (walk_snoc k 13 [13, 49] 71).symm
lemma arrow_span_136 (b : Fin 75) : a k b*normalRep k 136 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_136_69 k]
      exact normal_mem k 235
    · rw [extension_136_70 k]
      exact Submodule.zero_mem _
    · rw [extension_136_71 k]
      exact normal_mem k 236
  · rw [show a k b*normalRep k 136=0 from arrow_incompatible k b 13 43 [13, 49] (normal_endpoints 136) h]
    exact Submodule.zero_mem _
lemma extension_137_41 : a k 41*normalRep k 137=normalRep k 237 := by
  exact (walk_snoc k 14 [14, 9] 41).symm
lemma extension_137_42 : a k 42*normalRep k 137=0 := by
  change a k 42*walk k 14 [14, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_50 (a k) (relation_zero k) (e k 14)
lemma arrow_span_137 (b : Fin 75) : a k b*normalRep k 137 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_137_41 k]
      exact normal_mem k 237
    · rw [extension_137_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 137=0 from arrow_incompatible k b 14 31 [14, 9] (normal_endpoints 137) h]
    exact Submodule.zero_mem _
lemma extension_138_33 : a k 33*normalRep k 138=0 := by
  change a k 33*walk k 15 [15, 1]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_41 (a k) (relation_zero k) (e k 15)
lemma extension_138_34 : a k 34*normalRep k 138=normalRep k 238 := by
  exact (walk_snoc k 15 [15, 1] 34).symm
lemma arrow_span_138 (b : Fin 75) : a k b*normalRep k 138 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_138_33 k]
      exact Submodule.zero_mem _
    · rw [extension_138_34 k]
      exact normal_mem k 238
  · rw [show a k b*normalRep k 138=0 from arrow_incompatible k b 15 26 [15, 1] (normal_endpoints 138) h]
    exact Submodule.zero_mem _
lemma extension_139_5 : a k 5*normalRep k 139=normalRep k 238 := by
  change a k 5*walk k 15 [16, 57]=walk k 15 [15, 1, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_97 (a k) (relation_zero k) (e k 15)
lemma arrow_span_139 (b : Fin 75) : a k b*normalRep k 139 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_139_5 k]
      exact normal_mem k 238
  · rw [show a k b*normalRep k 139=0 from arrow_incompatible k b 15 5 [16, 57] (normal_endpoints 139) h]
    exact Submodule.zero_mem _
lemma extension_140_69 : a k 69*normalRep k 140=normalRep k 239 := by
  exact (walk_snoc k 16 [17, 21] 69).symm
lemma extension_140_70 : a k 70*normalRep k 140=normalRep k 240 := by
  exact (walk_snoc k 16 [17, 21] 70).symm
lemma extension_140_71 : a k 71*normalRep k 140=0 := by
  change a k 71*walk k 16 [17, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_60 (a k) (relation_zero k) (e k 16)
lemma arrow_span_140 (b : Fin 75) : a k b*normalRep k 140 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_140_69 k]
      exact normal_mem k 239
    · rw [extension_140_70 k]
      exact normal_mem k 240
    · rw [extension_140_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 140=0 from arrow_incompatible k b 16 43 [17, 21] (normal_endpoints 140) h]
    exact Submodule.zero_mem _
lemma extension_141_41 : a k 41*normalRep k 141=normalRep k 241 := by
  exact (walk_snoc k 17 [18, 9] 41).symm
lemma extension_141_42 : a k 42*normalRep k 141=0 := by
  change a k 42*walk k 17 [18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_51 (a k) (relation_zero k) (e k 17)
lemma arrow_span_141 (b : Fin 75) : a k b*normalRep k 141 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_141_41 k]
      exact normal_mem k 241
    · rw [extension_141_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 141=0 from arrow_incompatible k b 17 31 [18, 9] (normal_endpoints 141) h]
    exact Submodule.zero_mem _
lemma extension_142_54 : a k 54*normalRep k 142=normalRep k 242 := by
  exact (walk_snoc k 17 [19, 53] 54).symm
lemma extension_142_55 : a k 55*normalRep k 142=0 := by
  change a k 55*walk k 17 [19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_56 (a k) (relation_zero k) (e k 17)
lemma extension_142_56 : a k 56*normalRep k 142=normalRep k 241 := by
  change a k 56*walk k 17 [19, 53]=walk k 17 [18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_92 (a k) (relation_zero k) (e k 17)
lemma arrow_span_142 (b : Fin 75) : a k b*normalRep k 142 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_142_54 k]
      exact normal_mem k 242
    · rw [extension_142_55 k]
      exact Submodule.zero_mem _
    · rw [extension_142_56 k]
      exact normal_mem k 241
  · rw [show a k b*normalRep k 142=0 from arrow_incompatible k b 17 38 [19, 53] (normal_endpoints 142) h]
    exact Submodule.zero_mem _
lemma extension_143_2 : a k 2*normalRep k 143=normalRep k 243 := by
  exact (walk_snoc k 18 [20, 30] 2).symm
lemma arrow_span_143 (b : Fin 75) : a k b*normalRep k 143 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_143_2 k]
      exact normal_mem k 243
  · rw [show a k b*normalRep k 143=0 from arrow_incompatible k b 18 2 [20, 30] (normal_endpoints 143) h]
    exact Submodule.zero_mem _
lemma extension_144_8 : a k 8*normalRep k 144=normalRep k 244 := by
  exact (walk_snoc k 18 [21, 69] 8).symm
lemma arrow_span_144 (b : Fin 75) : a k b*normalRep k 144 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_144_8 k]
      exact normal_mem k 244
  · rw [show a k b*normalRep k 144=0 from arrow_incompatible k b 18 8 [21, 69] (normal_endpoints 144) h]
    exact Submodule.zero_mem _
lemma extension_145_22 : a k 22*normalRep k 145=normalRep k 245 := by
  exact (walk_snoc k 18 [21, 70] 22).symm
lemma extension_145_23 : a k 23*normalRep k 145=(-normalRep k 244) := by
  change a k 23*walk k 18 [21, 70]=(-walk k 18 [21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_109 (a k) (relation_zero k) (e k 18)
lemma arrow_span_145 (b : Fin 75) : a k b*normalRep k 145 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_145_22 k]
      exact normal_mem k 245
    · rw [extension_145_23 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 244)
  · rw [show a k b*normalRep k 145=0 from arrow_incompatible k b 18 19 [21, 70] (normal_endpoints 145) h]
    exact Submodule.zero_mem _
lemma extension_146_39 : a k 39*normalRep k 146=0 := by
  change a k 39*walk k 19 [22, 3]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_43 (a k) (relation_zero k) (e k 19)
lemma extension_146_40 : a k 40*normalRep k 146=normalRep k 246 := by
  exact (walk_snoc k 19 [22, 3] 40).symm
lemma arrow_span_146 (b : Fin 75) : a k b*normalRep k 146 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_146_39 k]
      exact Submodule.zero_mem _
    · rw [extension_146_40 k]
      exact normal_mem k 246
  · rw [show a k b*normalRep k 146=0 from arrow_incompatible k b 19 30 [22, 3] (normal_endpoints 146) h]
    exact Submodule.zero_mem _
lemma extension_147_24 : a k 24*normalRep k 147=normalRep k 247 := by
  exact (walk_snoc k 19 [23, 66] 24).symm
lemma extension_147_25 : a k 25*normalRep k 147=normalRep k 246 := by
  change a k 25*walk k 19 [23, 66]=walk k 19 [22, 3, 40]
  rw [← walk_snoc]
  exact Universal.mul_reduced_107 (a k) (relation_zero k) (e k 19)
lemma arrow_span_147 (b : Fin 75) : a k b*normalRep k 147 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_147_24 k]
      exact normal_mem k 247
    · rw [extension_147_25 k]
      exact normal_mem k 246
  · rw [show a k b*normalRep k 147=0 from arrow_incompatible k b 19 20 [23, 66] (normal_endpoints 147) h]
    exact Submodule.zero_mem _
lemma extension_148_9 : a k 9*normalRep k 148=normalRep k 248 := by
  exact (walk_snoc k 20 [24, 18] 9).symm
lemma arrow_span_148 (b : Fin 75) : a k b*normalRep k 148 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_148_9 k]
      exact normal_mem k 248
  · rw [show a k b*normalRep k 148=0 from arrow_incompatible k b 20 9 [24, 18] (normal_endpoints 148) h]
    exact Submodule.zero_mem _
lemma extension_149_52 : a k 52*normalRep k 149=normalRep k 248 := by
  change a k 52*walk k 20 [24, 19]=walk k 20 [24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_57 (a k) (relation_zero k) (e k 20)
lemma extension_149_53 : a k 53*normalRep k 149=normalRep k 249 := by
  exact (walk_snoc k 20 [24, 19] 53).symm
lemma arrow_span_149 (b : Fin 75) : a k b*normalRep k 149 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_149_52 k]
      exact normal_mem k 248
    · rw [extension_149_53 k]
      exact normal_mem k 249
  · rw [show a k b*normalRep k 149=0 from arrow_incompatible k b 20 37 [24, 19] (normal_endpoints 149) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
