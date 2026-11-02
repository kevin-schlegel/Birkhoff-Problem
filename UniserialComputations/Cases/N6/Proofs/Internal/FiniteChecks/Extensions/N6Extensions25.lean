import N6NormalData
import N6Reduced17
import N6Reduced18
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_1250_33 : a k 33*normalRep k 1250=0 := by
  change a k 33*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1027 (a k) (relation_zero k) (e k 6)
lemma extension_1250_34 : a k 34*normalRep k 1250=normalRep k 1317 := by
  change a k 34*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1074 (a k) (relation_zero k) (e k 6)
lemma arrow_span_1250 (b : Fin 75) : a k b*normalRep k 1250 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1250_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1250_34 k]
      exact normal_mem k 1317
  · rw [show a k b*normalRep k 1250=0 from arrow_incompatible k b 6 26 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1250) h]
    exact Submodule.zero_mem _
lemma extension_1251_63 : a k 63*normalRep k 1251=normalRep k 1318 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1251_64 : a k 64*normalRep k 1251=0 := by
  change a k 64*walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1030 (a k) (relation_zero k) (e k 7)
lemma extension_1251_65 : a k 65*normalRep k 1251=0 := by
  change a k 65*walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1040 (a k) (relation_zero k) (e k 7)
lemma arrow_span_1251 (b : Fin 75) : a k b*normalRep k 1251 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1251_63 k]
      exact normal_mem k 1318
    · rw [extension_1251_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1251_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1251=0 from arrow_incompatible k b 7 41 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1251) h]
    exact Submodule.zero_mem _
lemma extension_1252_0 : a k 0*normalRep k 1252=normalRep k 1319 := by
  exact (walk_snoc k 8 [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1252 (b : Fin 75) : a k b*normalRep k 1252 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1252_0 k]
      exact normal_mem k 1319
  · rw [show a k b*normalRep k 1252=0 from arrow_incompatible k b 8 0 [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1252) h]
    exact Submodule.zero_mem _
lemma extension_1253_13 : a k 13*normalRep k 1253=normalRep k 1320 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33] 13).symm
lemma arrow_span_1253 (b : Fin 75) : a k b*normalRep k 1253 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1253_13 k]
      exact normal_mem k 1320
  · rw [show a k b*normalRep k 1253=0 from arrow_incompatible k b 10 13 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33] (normal_endpoints 1253) h]
    exact Submodule.zero_mem _
lemma extension_1254_63 : a k 63*normalRep k 1254=normalRep k 1321 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] 63).symm
lemma extension_1254_64 : a k 64*normalRep k 1254=normalRep k 1322 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] 64).symm
lemma extension_1254_65 : a k 65*normalRep k 1254=normalRep k 1320 := by
  change a k 65*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1064 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1254 (b : Fin 75) : a k b*normalRep k 1254 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1254_63 k]
      exact normal_mem k 1321
    · rw [extension_1254_64 k]
      exact normal_mem k 1322
    · rw [extension_1254_65 k]
      exact normal_mem k 1320
  · rw [show a k b*normalRep k 1254=0 from arrow_incompatible k b 10 41 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] (normal_endpoints 1254) h]
    exact Submodule.zero_mem _
lemma extension_1255_17 : a k 17*normalRep k 1255=normalRep k 1321 := by
  change a k 17*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1069 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1255 (b : Fin 75) : a k b*normalRep k 1255 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1255_17 k]
      exact normal_mem k 1321
  · rw [show a k b*normalRep k 1255=0 from arrow_incompatible k b 10 16 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50] (normal_endpoints 1255) h]
    exact Submodule.zero_mem _
lemma extension_1256_49 : a k 49*normalRep k 1256=normalRep k 1323 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] 49).symm
lemma arrow_span_1256 (b : Fin 75) : a k b*normalRep k 1256 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1256_49 k]
      exact normal_mem k 1323
  · rw [show a k b*normalRep k 1256=0 from arrow_incompatible k b 11 35 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] (normal_endpoints 1256) h]
    exact Submodule.zero_mem _
lemma extension_1257_20 : a k 20*normalRep k 1257=0 := by
  change a k 20*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1050 (a k) (relation_zero k) (e k 11)
lemma extension_1257_21 : a k 21*normalRep k 1257=normalRep k 1324 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] 21).symm
lemma arrow_span_1257 (b : Fin 75) : a k b*normalRep k 1257 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1257_20 k]
      exact Submodule.zero_mem _
    · rw [extension_1257_21 k]
      exact normal_mem k 1324
  · rw [show a k b*normalRep k 1257=0 from arrow_incompatible k b 11 18 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] (normal_endpoints 1257) h]
    exact Submodule.zero_mem _
lemma extension_1258_36 : a k 36*normalRep k 1258=normalRep k 1324 + normalRep k 1323 := by
  change a k 36*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1080 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1258 (b : Fin 75) : a k b*normalRep k 1258 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1258_36 k]
      exact (normalSpan k).add_mem (normal_mem k 1324) (normal_mem k 1323)
  · rw [show a k b*normalRep k 1258=0 from arrow_incompatible k b 11 28 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64] (normal_endpoints 1258) h]
    exact Submodule.zero_mem _
lemma extension_1259_9 : a k 9*normalRep k 1259=normalRep k 1325 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1259 (b : Fin 75) : a k b*normalRep k 1259 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1259_9 k]
      exact normal_mem k 1325
  · rw [show a k b*normalRep k 1259=0 from arrow_incompatible k b 12 9 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1259) h]
    exact Submodule.zero_mem _
lemma extension_1260_52 : a k 52*normalRep k 1260=normalRep k 1325 := by
  change a k 52*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1051 (a k) (relation_zero k) (e k 12)
lemma extension_1260_53 : a k 53*normalRep k 1260=normalRep k 1326 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1260 (b : Fin 75) : a k b*normalRep k 1260 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1260_52 k]
      exact normal_mem k 1325
    · rw [extension_1260_53 k]
      exact normal_mem k 1326
  · rw [show a k b*normalRep k 1260=0 from arrow_incompatible k b 12 37 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1260) h]
    exact Submodule.zero_mem _
lemma extension_1261_4 : a k 4*normalRep k 1261=normalRep k 1326 := by
  change a k 4*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1078 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1261 (b : Fin 75) : a k b*normalRep k 1261 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1261_4 k]
      exact normal_mem k 1326
  · rw [show a k b*normalRep k 1261=0 from arrow_incompatible k b 12 4 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1261) h]
    exact Submodule.zero_mem _
lemma extension_1262_20 : a k 20*normalRep k 1262=normalRep k 1327 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1262_21 : a k 21*normalRep k 1262=0 := by
  change a k 21*walk k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1081 (a k) (relation_zero k) (e k 13)
lemma arrow_span_1262 (b : Fin 75) : a k b*normalRep k 1262 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1262_20 k]
      exact normal_mem k 1327
    · rw [extension_1262_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1262=0 from arrow_incompatible k b 13 18 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1262) h]
    exact Submodule.zero_mem _
lemma extension_1263_20 : a k 20*normalRep k 1263=normalRep k 1328 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1263_21 : a k 21*normalRep k 1263=0 := by
  change a k 21*walk k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1082 (a k) (relation_zero k) (e k 16)
lemma arrow_span_1263 (b : Fin 75) : a k b*normalRep k 1263 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1263_20 k]
      exact normal_mem k 1328
    · rw [extension_1263_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1263=0 from arrow_incompatible k b 16 18 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1263) h]
    exact Submodule.zero_mem _
lemma extension_1264_30 : a k 30*normalRep k 1264=normalRep k 1329 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1264_31 : a k 31*normalRep k 1264=0 := by
  change a k 31*walk k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1053 (a k) (relation_zero k) (e k 18)
lemma arrow_span_1264 (b : Fin 75) : a k b*normalRep k 1264 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1264_30 k]
      exact normal_mem k 1329
    · rw [extension_1264_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1264=0 from arrow_incompatible k b 18 24 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1264) h]
    exact Submodule.zero_mem _
lemma extension_1265_0 : a k 0*normalRep k 1265=normalRep k 1330 := by
  exact (walk_snoc k 19 [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2] 0).symm
lemma arrow_span_1265 (b : Fin 75) : a k b*normalRep k 1265 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1265_0 k]
      exact normal_mem k 1330
  · rw [show a k b*normalRep k 1265=0 from arrow_incompatible k b 19 0 [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2] (normal_endpoints 1265) h]
    exact Submodule.zero_mem _
lemma extension_1266_69 : a k 69*normalRep k 1266=normalRep k 1331 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 69).symm
lemma extension_1266_70 : a k 70*normalRep k 1266=0 := by
  change a k 70*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1068 (a k) (relation_zero k) (e k 21)
lemma extension_1266_71 : a k 71*normalRep k 1266=normalRep k 1332 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 71).symm
lemma arrow_span_1266 (b : Fin 75) : a k b*normalRep k 1266 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1266_69 k]
      exact normal_mem k 1331
    · rw [extension_1266_70 k]
      exact Submodule.zero_mem _
    · rw [extension_1266_71 k]
      exact normal_mem k 1332
  · rw [show a k b*normalRep k 1266=0 from arrow_incompatible k b 21 43 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] (normal_endpoints 1266) h]
    exact Submodule.zero_mem _
lemma extension_1267_69 : a k 69*normalRep k 1267=(-normalRep k 1331) := by
  change a k 69*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=(-walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1065 (a k) (relation_zero k) (e k 21)
lemma extension_1267_70 : a k 70*normalRep k 1267=normalRep k 1333 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] 70).symm
lemma extension_1267_71 : a k 71*normalRep k 1267=0 := by
  change a k 71*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1056 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1267 (b : Fin 75) : a k b*normalRep k 1267 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1267_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1331)
    · rw [extension_1267_70 k]
      exact normal_mem k 1333
    · rw [extension_1267_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1267=0 from arrow_incompatible k b 21 43 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] (normal_endpoints 1267) h]
    exact Submodule.zero_mem _
lemma extension_1268_57 : a k 57*normalRep k 1268=normalRep k 1334 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1268_58 : a k 58*normalRep k 1268=normalRep k 1335 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1268_59 : a k 59*normalRep k 1268=0 := by
  change a k 59*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1047 (a k) (relation_zero k) (e k 22)
lemma arrow_span_1268 (b : Fin 75) : a k b*normalRep k 1268 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1268_57 k]
      exact normal_mem k 1334
    · rw [extension_1268_58 k]
      exact normal_mem k 1335
    · rw [extension_1268_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1268=0 from arrow_incompatible k b 22 39 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1268) h]
    exact Submodule.zero_mem _
lemma extension_1269_1 : a k 1*normalRep k 1269=normalRep k 1335 := by
  change a k 1*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1044 (a k) (relation_zero k) (e k 22)
lemma arrow_span_1269 (b : Fin 75) : a k b*normalRep k 1269 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1269_1 k]
      exact normal_mem k 1335
  · rw [show a k b*normalRep k 1269=0 from arrow_incompatible k b 22 1 [27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1269) h]
    exact Submodule.zero_mem _
lemma extension_1270_8 : a k 8*normalRep k 1270=normalRep k 1336 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_1270 (b : Fin 75) : a k b*normalRep k 1270 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1270_8 k]
      exact normal_mem k 1336
  · rw [show a k b*normalRep k 1270=0 from arrow_incompatible k b 24 8 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] (normal_endpoints 1270) h]
    exact Submodule.zero_mem _
lemma extension_1271_72 : a k 72*normalRep k 1271=normalRep k 1337 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] 72).symm
lemma extension_1271_73 : a k 73*normalRep k 1271=normalRep k 1336 := by
  change a k 73*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1085 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1271 (b : Fin 75) : a k b*normalRep k 1271 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1271_72 k]
      exact normal_mem k 1337
    · rw [extension_1271_73 k]
      exact normal_mem k 1336
  · rw [show a k b*normalRep k 1271=0 from arrow_incompatible k b 24 44 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] (normal_endpoints 1271) h]
    exact Submodule.zero_mem _
lemma extension_1272_22 : a k 22*normalRep k 1272=normalRep k 1338 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] 22).symm
lemma extension_1272_23 : a k 23*normalRep k 1272=normalRep k 1336 := by
  change a k 23*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1086 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1272 (b : Fin 75) : a k b*normalRep k 1272 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1272_22 k]
      exact normal_mem k 1338
    · rw [extension_1272_23 k]
      exact normal_mem k 1336
  · rw [show a k b*normalRep k 1272=0 from arrow_incompatible k b 24 19 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] (normal_endpoints 1272) h]
    exact Submodule.zero_mem _
lemma extension_1273_18 : a k 18*normalRep k 1273=normalRep k 1339 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_1273_19 : a k 19*normalRep k 1273=normalRep k 1340 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_1273 (b : Fin 75) : a k b*normalRep k 1273 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1273_18 k]
      exact normal_mem k 1339
    · rw [extension_1273_19 k]
      exact normal_mem k 1340
  · rw [show a k b*normalRep k 1273=0 from arrow_incompatible k b 25 17 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 1273) h]
    exact Submodule.zero_mem _
lemma extension_1274_60 : a k 60*normalRep k 1274=normalRep k 1341 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_1274_61 : a k 61*normalRep k 1274=0 := by
  change a k 61*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1058 (a k) (relation_zero k) (e k 25)
lemma extension_1274_62 : a k 62*normalRep k 1274=normalRep k 1340 := by
  change a k 62*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1060 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1274 (b : Fin 75) : a k b*normalRep k 1274 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1274_60 k]
      exact normal_mem k 1341
    · rw [extension_1274_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1274_62 k]
      exact normal_mem k 1340
  · rw [show a k b*normalRep k 1274=0 from arrow_incompatible k b 25 40 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 1274) h]
    exact Submodule.zero_mem _
lemma extension_1275_14 : a k 14*normalRep k 1275=normalRep k 1339 := by
  change a k 14*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1062 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1275 (b : Fin 75) : a k b*normalRep k 1275 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1275_14 k]
      exact normal_mem k 1339
  · rw [show a k b*normalRep k 1275=0 from arrow_incompatible k b 25 14 [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 1275) h]
    exact Submodule.zero_mem _
lemma extension_1276_63 : a k 63*normalRep k 1276=normalRep k 1342 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1276_64 : a k 64*normalRep k 1276=0 := by
  change a k 64*walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1031 (a k) (relation_zero k) (e k 26)
lemma extension_1276_65 : a k 65*normalRep k 1276=0 := by
  change a k 65*walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1041 (a k) (relation_zero k) (e k 26)
lemma arrow_span_1276 (b : Fin 75) : a k b*normalRep k 1276 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1276_63 k]
      exact normal_mem k 1342
    · rw [extension_1276_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1276_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1276=0 from arrow_incompatible k b 26 41 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1276) h]
    exact Submodule.zero_mem _
lemma extension_1277_41 : a k 41*normalRep k 1277=normalRep k 1343 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1277_42 : a k 42*normalRep k 1277=0 := by
  change a k 42*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1034 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1277 (b : Fin 75) : a k b*normalRep k 1277 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1277_41 k]
      exact normal_mem k 1343
    · rw [extension_1277_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1277=0 from arrow_incompatible k b 27 31 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1277) h]
    exact Submodule.zero_mem _
lemma extension_1278_54 : a k 54*normalRep k 1278=normalRep k 1344 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1278_55 : a k 55*normalRep k 1278=0 := by
  change a k 55*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1036 (a k) (relation_zero k) (e k 27)
lemma extension_1278_56 : a k 56*normalRep k 1278=normalRep k 1343 := by
  change a k 56*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1070 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1278 (b : Fin 75) : a k b*normalRep k 1278 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1278_54 k]
      exact normal_mem k 1344
    · rw [extension_1278_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1278_56 k]
      exact normal_mem k 1343
  · rw [show a k b*normalRep k 1278=0 from arrow_incompatible k b 27 38 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1278) h]
    exact Submodule.zero_mem _
lemma extension_1279_30 : a k 30*normalRep k 1279=normalRep k 1345 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20] 30).symm
lemma extension_1279_31 : a k 31*normalRep k 1279=0 := by
  change a k 31*walk k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1054 (a k) (relation_zero k) (e k 28)
lemma arrow_span_1279 (b : Fin 75) : a k b*normalRep k 1279 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1279_30 k]
      exact normal_mem k 1345
    · rw [extension_1279_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1279=0 from arrow_incompatible k b 28 24 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20] (normal_endpoints 1279) h]
    exact Submodule.zero_mem _
lemma arrow_span_1280 (b : Fin 75) : a k b*normalRep k 1280 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1280=0 from arrow_incompatible k b 29 46 [37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1280) h]
    exact Submodule.zero_mem _
lemma extension_1281_18 : a k 18*normalRep k 1281=normalRep k 1346 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_1281_19 : a k 19*normalRep k 1281=normalRep k 1347 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_1281 (b : Fin 75) : a k b*normalRep k 1281 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1281_18 k]
      exact normal_mem k 1346
    · rw [extension_1281_19 k]
      exact normal_mem k 1347
  · rw [show a k b*normalRep k 1281=0 from arrow_incompatible k b 30 17 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 1281) h]
    exact Submodule.zero_mem _
lemma extension_1282_60 : a k 60*normalRep k 1282=normalRep k 1348 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_1282_61 : a k 61*normalRep k 1282=0 := by
  change a k 61*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1059 (a k) (relation_zero k) (e k 30)
lemma extension_1282_62 : a k 62*normalRep k 1282=normalRep k 1347 := by
  change a k 62*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1061 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1282 (b : Fin 75) : a k b*normalRep k 1282 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1282_60 k]
      exact normal_mem k 1348
    · rw [extension_1282_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1282_62 k]
      exact normal_mem k 1347
  · rw [show a k b*normalRep k 1282=0 from arrow_incompatible k b 30 40 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 1282) h]
    exact Submodule.zero_mem _
lemma extension_1283_14 : a k 14*normalRep k 1283=normalRep k 1346 := by
  change a k 14*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1063 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1283 (b : Fin 75) : a k b*normalRep k 1283 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1283_14 k]
      exact normal_mem k 1346
  · rw [show a k b*normalRep k 1283=0 from arrow_incompatible k b 30 14 [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 1283) h]
    exact Submodule.zero_mem _
lemma extension_1284_43 : a k 43*normalRep k 1284=0 := by
  change a k 43*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1038 (a k) (relation_zero k) (e k 31)
lemma extension_1284_44 : a k 44*normalRep k 1284=normalRep k 1349 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1284 (b : Fin 75) : a k b*normalRep k 1284 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1284_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1284_44 k]
      exact normal_mem k 1349
  · rw [show a k b*normalRep k 1284=0 from arrow_incompatible k b 31 32 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1284) h]
    exact Submodule.zero_mem _
lemma extension_1285_15 : a k 15*normalRep k 1285=normalRep k 1350 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1285_16 : a k 16*normalRep k 1285=normalRep k 1349 := by
  change a k 16*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]=walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1072 (a k) (relation_zero k) (e k 31)
lemma arrow_span_1285 (b : Fin 75) : a k b*normalRep k 1285 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1285_15 k]
      exact normal_mem k 1350
    · rw [extension_1285_16 k]
      exact normal_mem k 1349
  · rw [show a k b*normalRep k 1285=0 from arrow_incompatible k b 31 15 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1285) h]
    exact Submodule.zero_mem _
lemma extension_1286_57 : a k 57*normalRep k 1286=normalRep k 1351 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1286_58 : a k 58*normalRep k 1286=normalRep k 1352 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1286_59 : a k 59*normalRep k 1286=0 := by
  change a k 59*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1048 (a k) (relation_zero k) (e k 32)
lemma arrow_span_1286 (b : Fin 75) : a k b*normalRep k 1286 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1286_57 k]
      exact normal_mem k 1351
    · rw [extension_1286_58 k]
      exact normal_mem k 1352
    · rw [extension_1286_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1286=0 from arrow_incompatible k b 32 39 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1286) h]
    exact Submodule.zero_mem _
lemma extension_1287_1 : a k 1*normalRep k 1287=normalRep k 1352 := by
  change a k 1*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1045 (a k) (relation_zero k) (e k 32)
lemma arrow_span_1287 (b : Fin 75) : a k b*normalRep k 1287 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1287_1 k]
      exact normal_mem k 1352
  · rw [show a k b*normalRep k 1287=0 from arrow_incompatible k b 32 1 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1287) h]
    exact Submodule.zero_mem _
lemma extension_1288_57 : a k 57*normalRep k 1288=normalRep k 1353 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1288_58 : a k 58*normalRep k 1288=normalRep k 1354 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1288_59 : a k 59*normalRep k 1288=0 := by
  change a k 59*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1049 (a k) (relation_zero k) (e k 33)
lemma arrow_span_1288 (b : Fin 75) : a k b*normalRep k 1288 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1288_57 k]
      exact normal_mem k 1353
    · rw [extension_1288_58 k]
      exact normal_mem k 1354
    · rw [extension_1288_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1288=0 from arrow_incompatible k b 33 39 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1288) h]
    exact Submodule.zero_mem _
lemma extension_1289_1 : a k 1*normalRep k 1289=normalRep k 1354 := by
  change a k 1*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1046 (a k) (relation_zero k) (e k 33)
lemma arrow_span_1289 (b : Fin 75) : a k b*normalRep k 1289 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1289_1 k]
      exact normal_mem k 1354
  · rw [show a k b*normalRep k 1289=0 from arrow_incompatible k b 33 1 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1289) h]
    exact Submodule.zero_mem _
lemma extension_1290_5 : a k 5*normalRep k 1290=normalRep k 1355 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1290 (b : Fin 75) : a k b*normalRep k 1290 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1290_5 k]
      exact normal_mem k 1355
  · rw [show a k b*normalRep k 1290=0 from arrow_incompatible k b 34 5 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1290) h]
    exact Submodule.zero_mem _
lemma extension_1291_33 : a k 33*normalRep k 1291=0 := by
  change a k 33*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1028 (a k) (relation_zero k) (e k 34)
lemma extension_1291_34 : a k 34*normalRep k 1291=normalRep k 1355 := by
  change a k 34*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1075 (a k) (relation_zero k) (e k 34)
lemma arrow_span_1291 (b : Fin 75) : a k b*normalRep k 1291 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1291_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1291_34 k]
      exact normal_mem k 1355
  · rw [show a k b*normalRep k 1291=0 from arrow_incompatible k b 34 26 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1291) h]
    exact Submodule.zero_mem _
lemma extension_1292_30 : a k 30*normalRep k 1292=normalRep k 1356 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1292_31 : a k 31*normalRep k 1292=0 := by
  change a k 31*walk k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1055 (a k) (relation_zero k) (e k 35)
lemma arrow_span_1292 (b : Fin 75) : a k b*normalRep k 1292 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1292_30 k]
      exact normal_mem k 1356
    · rw [extension_1292_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1292=0 from arrow_incompatible k b 35 24 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1292) h]
    exact Submodule.zero_mem _
lemma extension_1293_63 : a k 63*normalRep k 1293=normalRep k 1357 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1293_64 : a k 64*normalRep k 1293=0 := by
  change a k 64*walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1032 (a k) (relation_zero k) (e k 36)
lemma extension_1293_65 : a k 65*normalRep k 1293=0 := by
  change a k 65*walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1042 (a k) (relation_zero k) (e k 36)
lemma arrow_span_1293 (b : Fin 75) : a k b*normalRep k 1293 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1293_63 k]
      exact normal_mem k 1357
    · rw [extension_1293_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1293_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1293=0 from arrow_incompatible k b 36 41 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1293) h]
    exact Submodule.zero_mem _
lemma extension_1294_41 : a k 41*normalRep k 1294=normalRep k 1358 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1294_42 : a k 42*normalRep k 1294=0 := by
  change a k 42*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1035 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1294 (b : Fin 75) : a k b*normalRep k 1294 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1294_41 k]
      exact normal_mem k 1358
    · rw [extension_1294_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1294=0 from arrow_incompatible k b 37 31 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9] (normal_endpoints 1294) h]
    exact Submodule.zero_mem _
lemma extension_1295_54 : a k 54*normalRep k 1295=normalRep k 1359 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1295_55 : a k 55*normalRep k 1295=0 := by
  change a k 55*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1037 (a k) (relation_zero k) (e k 37)
lemma extension_1295_56 : a k 56*normalRep k 1295=normalRep k 1358 := by
  change a k 56*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]=walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1071 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1295 (b : Fin 75) : a k b*normalRep k 1295 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1295_54 k]
      exact normal_mem k 1359
    · rw [extension_1295_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1295_56 k]
      exact normal_mem k 1358
  · rw [show a k b*normalRep k 1295=0 from arrow_incompatible k b 37 38 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53] (normal_endpoints 1295) h]
    exact Submodule.zero_mem _
lemma extension_1296_43 : a k 43*normalRep k 1296=0 := by
  change a k 43*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1039 (a k) (relation_zero k) (e k 38)
lemma extension_1296_44 : a k 44*normalRep k 1296=normalRep k 1360 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1296 (b : Fin 75) : a k b*normalRep k 1296 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1296_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1296_44 k]
      exact normal_mem k 1360
  · rw [show a k b*normalRep k 1296=0 from arrow_incompatible k b 38 32 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1296) h]
    exact Submodule.zero_mem _
lemma extension_1297_15 : a k 15*normalRep k 1297=normalRep k 1361 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1297_16 : a k 16*normalRep k 1297=normalRep k 1360 := by
  change a k 16*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1073 (a k) (relation_zero k) (e k 38)
lemma arrow_span_1297 (b : Fin 75) : a k b*normalRep k 1297 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1297_15 k]
      exact normal_mem k 1361
    · rw [extension_1297_16 k]
      exact normal_mem k 1360
  · rw [show a k b*normalRep k 1297=0 from arrow_incompatible k b 38 15 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1297) h]
    exact Submodule.zero_mem _
lemma extension_1298_5 : a k 5*normalRep k 1298=normalRep k 1362 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1298 (b : Fin 75) : a k b*normalRep k 1298 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1298_5 k]
      exact normal_mem k 1362
  · rw [show a k b*normalRep k 1298=0 from arrow_incompatible k b 39 5 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1298) h]
    exact Submodule.zero_mem _
lemma extension_1299_33 : a k 33*normalRep k 1299=0 := by
  change a k 33*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1029 (a k) (relation_zero k) (e k 39)
lemma extension_1299_34 : a k 34*normalRep k 1299=normalRep k 1362 := by
  change a k 34*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1076 (a k) (relation_zero k) (e k 39)
lemma arrow_span_1299 (b : Fin 75) : a k b*normalRep k 1299 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1299_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1299_34 k]
      exact normal_mem k 1362
  · rw [show a k b*normalRep k 1299=0 from arrow_incompatible k b 39 26 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1299) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
