import N6NormalData
import N6Reduced16
import N6Reduced17
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_1200_39 : a k 39*normalRep k 1200=0 := by
  change a k 39*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_965 (a k) (relation_zero k) (e k 25)
lemma extension_1200_40 : a k 40*normalRep k 1200=(-normalRep k 1274) := by
  change a k 40*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1022 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1200 (b : Fin 75) : a k b*normalRep k 1200 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1200_39 k]
      exact Submodule.zero_mem _
    · rw [extension_1200_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1274)
  · rw [show a k b*normalRep k 1200=0 from arrow_incompatible k b 25 30 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 1200) h]
    exact Submodule.zero_mem _
lemma extension_1201_28 : a k 28*normalRep k 1201=normalRep k 1275 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_1201_29 : a k 29*normalRep k 1201=normalRep k 1273 := by
  change a k 29*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]=walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1000 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1201 (b : Fin 75) : a k b*normalRep k 1201 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1201_28 k]
      exact normal_mem k 1275
    · rw [extension_1201_29 k]
      exact normal_mem k 1273
  · rw [show a k b*normalRep k 1201=0 from arrow_incompatible k b 25 23 [32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 1201) h]
    exact Submodule.zero_mem _
lemma extension_1202_5 : a k 5*normalRep k 1202=normalRep k 1276 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1202 (b : Fin 75) : a k b*normalRep k 1202 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1202_5 k]
      exact normal_mem k 1276
  · rw [show a k b*normalRep k 1202=0 from arrow_incompatible k b 26 5 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1202) h]
    exact Submodule.zero_mem _
lemma extension_1203_33 : a k 33*normalRep k 1203=0 := by
  change a k 33*walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_960 (a k) (relation_zero k) (e k 26)
lemma extension_1203_34 : a k 34*normalRep k 1203=normalRep k 1276 := by
  change a k 34*walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1014 (a k) (relation_zero k) (e k 26)
lemma arrow_span_1203 (b : Fin 75) : a k b*normalRep k 1203 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1203_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1203_34 k]
      exact normal_mem k 1276
  · rw [show a k b*normalRep k 1203=0 from arrow_incompatible k b 26 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1203) h]
    exact Submodule.zero_mem _
lemma extension_1204_9 : a k 9*normalRep k 1204=normalRep k 1277 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1204 (b : Fin 75) : a k b*normalRep k 1204 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1204_9 k]
      exact normal_mem k 1277
  · rw [show a k b*normalRep k 1204=0 from arrow_incompatible k b 27 9 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1204) h]
    exact Submodule.zero_mem _
lemma extension_1205_52 : a k 52*normalRep k 1205=normalRep k 1277 := by
  change a k 52*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_985 (a k) (relation_zero k) (e k 27)
lemma extension_1205_53 : a k 53*normalRep k 1205=normalRep k 1278 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1205 (b : Fin 75) : a k b*normalRep k 1205 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1205_52 k]
      exact normal_mem k 1277
    · rw [extension_1205_53 k]
      exact normal_mem k 1278
  · rw [show a k b*normalRep k 1205=0 from arrow_incompatible k b 27 37 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1205) h]
    exact Submodule.zero_mem _
lemma extension_1206_4 : a k 4*normalRep k 1206=normalRep k 1278 := by
  change a k 4*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1016 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1206 (b : Fin 75) : a k b*normalRep k 1206 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1206_4 k]
      exact normal_mem k 1278
  · rw [show a k b*normalRep k 1206=0 from arrow_incompatible k b 27 4 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1206) h]
    exact Submodule.zero_mem _
lemma extension_1207_20 : a k 20*normalRep k 1207=normalRep k 1279 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63] 20).symm
lemma extension_1207_21 : a k 21*normalRep k 1207=0 := by
  change a k 21*walk k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1020 (a k) (relation_zero k) (e k 28)
lemma arrow_span_1207 (b : Fin 75) : a k b*normalRep k 1207 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1207_20 k]
      exact normal_mem k 1279
    · rw [extension_1207_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1207=0 from arrow_incompatible k b 28 18 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63] (normal_endpoints 1207) h]
    exact Submodule.zero_mem _
lemma extension_1208_0 : a k 0*normalRep k 1208=normalRep k 1280 := by
  exact (walk_snoc k 29 [37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1208 (b : Fin 75) : a k b*normalRep k 1208 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1208_0 k]
      exact normal_mem k 1280
  · rw [show a k b*normalRep k 1208=0 from arrow_incompatible k b 29 0 [37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1208) h]
    exact Submodule.zero_mem _
lemma extension_1209_24 : a k 24*normalRep k 1209=normalRep k 1281 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_1209_25 : a k 25*normalRep k 1209=normalRep k 1282 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_1209 (b : Fin 75) : a k b*normalRep k 1209 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1209_24 k]
      exact normal_mem k 1281
    · rw [extension_1209_25 k]
      exact normal_mem k 1282
  · rw [show a k b*normalRep k 1209=0 from arrow_incompatible k b 30 20 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 1209) h]
    exact Submodule.zero_mem _
lemma extension_1210_39 : a k 39*normalRep k 1210=0 := by
  change a k 39*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_966 (a k) (relation_zero k) (e k 30)
lemma extension_1210_40 : a k 40*normalRep k 1210=(-normalRep k 1282) := by
  change a k 40*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1023 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1210 (b : Fin 75) : a k b*normalRep k 1210 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1210_39 k]
      exact Submodule.zero_mem _
    · rw [extension_1210_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1282)
  · rw [show a k b*normalRep k 1210=0 from arrow_incompatible k b 30 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 1210) h]
    exact Submodule.zero_mem _
lemma extension_1211_28 : a k 28*normalRep k 1211=normalRep k 1283 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_1211_29 : a k 29*normalRep k 1211=normalRep k 1281 := by
  change a k 29*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]=walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1001 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1211 (b : Fin 75) : a k b*normalRep k 1211 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1211_28 k]
      exact normal_mem k 1283
    · rw [extension_1211_29 k]
      exact normal_mem k 1281
  · rw [show a k b*normalRep k 1211=0 from arrow_incompatible k b 30 23 [39, 12, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 1211) h]
    exact Submodule.zero_mem _
lemma arrow_span_1212 (b : Fin 75) : a k b*normalRep k 1212 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1212=0 from arrow_incompatible k b 30 46 [40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2, 0] (normal_endpoints 1212) h]
    exact Submodule.zero_mem _
lemma extension_1213_41 : a k 41*normalRep k 1213=normalRep k 1284 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1213_42 : a k 42*normalRep k 1213=0 := by
  change a k 42*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_967 (a k) (relation_zero k) (e k 31)
lemma arrow_span_1213 (b : Fin 75) : a k b*normalRep k 1213 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1213_41 k]
      exact normal_mem k 1284
    · rw [extension_1213_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1213=0 from arrow_incompatible k b 31 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9] (normal_endpoints 1213) h]
    exact Submodule.zero_mem _
lemma extension_1214_54 : a k 54*normalRep k 1214=normalRep k 1285 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1214_55 : a k 55*normalRep k 1214=0 := by
  change a k 55*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_969 (a k) (relation_zero k) (e k 31)
lemma extension_1214_56 : a k 56*normalRep k 1214=normalRep k 1284 := by
  change a k 56*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]=walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1007 (a k) (relation_zero k) (e k 31)
lemma arrow_span_1214 (b : Fin 75) : a k b*normalRep k 1214 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1214_54 k]
      exact normal_mem k 1285
    · rw [extension_1214_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1214_56 k]
      exact normal_mem k 1284
  · rw [show a k b*normalRep k 1214=0 from arrow_incompatible k b 31 38 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53] (normal_endpoints 1214) h]
    exact Submodule.zero_mem _
lemma extension_1215_43 : a k 43*normalRep k 1215=0 := by
  change a k 43*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_972 (a k) (relation_zero k) (e k 32)
lemma extension_1215_44 : a k 44*normalRep k 1215=normalRep k 1286 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1215 (b : Fin 75) : a k b*normalRep k 1215 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1215_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1215_44 k]
      exact normal_mem k 1286
  · rw [show a k b*normalRep k 1215=0 from arrow_incompatible k b 32 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1215) h]
    exact Submodule.zero_mem _
lemma extension_1216_15 : a k 15*normalRep k 1216=normalRep k 1287 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1216_16 : a k 16*normalRep k 1216=normalRep k 1286 := by
  change a k 16*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]=walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1010 (a k) (relation_zero k) (e k 32)
lemma arrow_span_1216 (b : Fin 75) : a k b*normalRep k 1216 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1216_15 k]
      exact normal_mem k 1287
    · rw [extension_1216_16 k]
      exact normal_mem k 1286
  · rw [show a k b*normalRep k 1216=0 from arrow_incompatible k b 32 15 [43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1216) h]
    exact Submodule.zero_mem _
lemma extension_1217_43 : a k 43*normalRep k 1217=0 := by
  change a k 43*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_973 (a k) (relation_zero k) (e k 33)
lemma extension_1217_44 : a k 44*normalRep k 1217=normalRep k 1288 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1217 (b : Fin 75) : a k b*normalRep k 1217 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1217_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1217_44 k]
      exact normal_mem k 1288
  · rw [show a k b*normalRep k 1217=0 from arrow_incompatible k b 33 32 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1217) h]
    exact Submodule.zero_mem _
lemma extension_1218_15 : a k 15*normalRep k 1218=normalRep k 1289 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1218_16 : a k 16*normalRep k 1218=normalRep k 1288 := by
  change a k 16*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]=walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1011 (a k) (relation_zero k) (e k 33)
lemma arrow_span_1218 (b : Fin 75) : a k b*normalRep k 1218 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1218_15 k]
      exact normal_mem k 1289
    · rw [extension_1218_16 k]
      exact normal_mem k 1288
  · rw [show a k b*normalRep k 1218=0 from arrow_incompatible k b 33 15 [45, 6, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1218) h]
    exact Submodule.zero_mem _
lemma extension_1219_57 : a k 57*normalRep k 1219=normalRep k 1290 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1219_58 : a k 58*normalRep k 1219=normalRep k 1291 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1219_59 : a k 59*normalRep k 1219=0 := by
  change a k 59*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_982 (a k) (relation_zero k) (e k 34)
lemma arrow_span_1219 (b : Fin 75) : a k b*normalRep k 1219 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1219_57 k]
      exact normal_mem k 1290
    · rw [extension_1219_58 k]
      exact normal_mem k 1291
    · rw [extension_1219_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1219=0 from arrow_incompatible k b 34 39 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1219) h]
    exact Submodule.zero_mem _
lemma extension_1220_1 : a k 1*normalRep k 1220=normalRep k 1291 := by
  change a k 1*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_979 (a k) (relation_zero k) (e k 34)
lemma arrow_span_1220 (b : Fin 75) : a k b*normalRep k 1220 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1220_1 k]
      exact normal_mem k 1291
  · rw [show a k b*normalRep k 1220=0 from arrow_incompatible k b 34 1 [47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1220) h]
    exact Submodule.zero_mem _
lemma extension_1221_20 : a k 20*normalRep k 1221=normalRep k 1292 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1221_21 : a k 21*normalRep k 1221=0 := by
  change a k 21*walk k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1021 (a k) (relation_zero k) (e k 35)
lemma arrow_span_1221 (b : Fin 75) : a k b*normalRep k 1221 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1221_20 k]
      exact normal_mem k 1292
    · rw [extension_1221_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1221=0 from arrow_incompatible k b 35 18 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1221) h]
    exact Submodule.zero_mem _
lemma extension_1222_5 : a k 5*normalRep k 1222=normalRep k 1293 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1222 (b : Fin 75) : a k b*normalRep k 1222 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1222_5 k]
      exact normal_mem k 1293
  · rw [show a k b*normalRep k 1222=0 from arrow_incompatible k b 36 5 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1222) h]
    exact Submodule.zero_mem _
lemma extension_1223_33 : a k 33*normalRep k 1223=0 := by
  change a k 33*walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_961 (a k) (relation_zero k) (e k 36)
lemma extension_1223_34 : a k 34*normalRep k 1223=normalRep k 1293 := by
  change a k 34*walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1015 (a k) (relation_zero k) (e k 36)
lemma arrow_span_1223 (b : Fin 75) : a k b*normalRep k 1223 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1223_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1223_34 k]
      exact normal_mem k 1293
  · rw [show a k b*normalRep k 1223=0 from arrow_incompatible k b 36 26 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1223) h]
    exact Submodule.zero_mem _
lemma extension_1224_9 : a k 9*normalRep k 1224=normalRep k 1294 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1224 (b : Fin 75) : a k b*normalRep k 1224 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1224_9 k]
      exact normal_mem k 1294
  · rw [show a k b*normalRep k 1224=0 from arrow_incompatible k b 37 9 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18] (normal_endpoints 1224) h]
    exact Submodule.zero_mem _
lemma extension_1225_52 : a k 52*normalRep k 1225=normalRep k 1294 := by
  change a k 52*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19]=walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_986 (a k) (relation_zero k) (e k 37)
lemma extension_1225_53 : a k 53*normalRep k 1225=normalRep k 1295 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1225 (b : Fin 75) : a k b*normalRep k 1225 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1225_52 k]
      exact normal_mem k 1294
    · rw [extension_1225_53 k]
      exact normal_mem k 1295
  · rw [show a k b*normalRep k 1225=0 from arrow_incompatible k b 37 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19] (normal_endpoints 1225) h]
    exact Submodule.zero_mem _
lemma extension_1226_4 : a k 4*normalRep k 1226=normalRep k 1295 := by
  change a k 4*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60]=walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1017 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1226 (b : Fin 75) : a k b*normalRep k 1226 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1226_4 k]
      exact normal_mem k 1295
  · rw [show a k b*normalRep k 1226=0 from arrow_incompatible k b 37 4 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 25, 60] (normal_endpoints 1226) h]
    exact Submodule.zero_mem _
lemma extension_1227_41 : a k 41*normalRep k 1227=normalRep k 1296 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1227_42 : a k 42*normalRep k 1227=0 := by
  change a k 42*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_968 (a k) (relation_zero k) (e k 38)
lemma arrow_span_1227 (b : Fin 75) : a k b*normalRep k 1227 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1227_41 k]
      exact normal_mem k 1296
    · rw [extension_1227_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1227=0 from arrow_incompatible k b 38 31 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1227) h]
    exact Submodule.zero_mem _
lemma extension_1228_54 : a k 54*normalRep k 1228=normalRep k 1297 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1228_55 : a k 55*normalRep k 1228=0 := by
  change a k 55*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_970 (a k) (relation_zero k) (e k 38)
lemma extension_1228_56 : a k 56*normalRep k 1228=normalRep k 1296 := by
  change a k 56*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1008 (a k) (relation_zero k) (e k 38)
lemma arrow_span_1228 (b : Fin 75) : a k b*normalRep k 1228 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1228_54 k]
      exact normal_mem k 1297
    · rw [extension_1228_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1228_56 k]
      exact normal_mem k 1296
  · rw [show a k b*normalRep k 1228=0 from arrow_incompatible k b 38 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1228) h]
    exact Submodule.zero_mem _
lemma extension_1229_57 : a k 57*normalRep k 1229=normalRep k 1298 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1229_58 : a k 58*normalRep k 1229=normalRep k 1299 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1229_59 : a k 59*normalRep k 1229=0 := by
  change a k 59*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_983 (a k) (relation_zero k) (e k 39)
lemma arrow_span_1229 (b : Fin 75) : a k b*normalRep k 1229 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1229_57 k]
      exact normal_mem k 1298
    · rw [extension_1229_58 k]
      exact normal_mem k 1299
    · rw [extension_1229_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1229=0 from arrow_incompatible k b 39 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1229) h]
    exact Submodule.zero_mem _
lemma extension_1230_1 : a k 1*normalRep k 1230=normalRep k 1299 := by
  change a k 1*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_980 (a k) (relation_zero k) (e k 39)
lemma arrow_span_1230 (b : Fin 75) : a k b*normalRep k 1230 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1230_1 k]
      exact normal_mem k 1299
  · rw [show a k b*normalRep k 1230=0 from arrow_incompatible k b 39 1 [58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1230) h]
    exact Submodule.zero_mem _
lemma extension_1231_18 : a k 18*normalRep k 1231=normalRep k 1300 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_1231_19 : a k 19*normalRep k 1231=normalRep k 1301 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_1231 (b : Fin 75) : a k b*normalRep k 1231 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1231_18 k]
      exact normal_mem k 1300
    · rw [extension_1231_19 k]
      exact normal_mem k 1301
  · rw [show a k b*normalRep k 1231=0 from arrow_incompatible k b 40 17 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 1231) h]
    exact Submodule.zero_mem _
lemma extension_1232_60 : a k 60*normalRep k 1232=normalRep k 1302 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_1232_61 : a k 61*normalRep k 1232=0 := by
  change a k 61*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_992 (a k) (relation_zero k) (e k 40)
lemma extension_1232_62 : a k 62*normalRep k 1232=normalRep k 1301 := by
  change a k 62*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_994 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1232 (b : Fin 75) : a k b*normalRep k 1232 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1232_60 k]
      exact normal_mem k 1302
    · rw [extension_1232_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1232_62 k]
      exact normal_mem k 1301
  · rw [show a k b*normalRep k 1232=0 from arrow_incompatible k b 40 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 1232) h]
    exact Submodule.zero_mem _
lemma extension_1233_14 : a k 14*normalRep k 1233=normalRep k 1300 := by
  change a k 14*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_997 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1233 (b : Fin 75) : a k b*normalRep k 1233 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1233_14 k]
      exact normal_mem k 1300
  · rw [show a k b*normalRep k 1233=0 from arrow_incompatible k b 40 14 [61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 1233) h]
    exact Submodule.zero_mem _
lemma extension_1234_63 : a k 63*normalRep k 1234=normalRep k 1303 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1234_64 : a k 64*normalRep k 1234=0 := by
  change a k 64*walk k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_964 (a k) (relation_zero k) (e k 41)
lemma extension_1234_65 : a k 65*normalRep k 1234=0 := by
  change a k 65*walk k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_976 (a k) (relation_zero k) (e k 41)
lemma arrow_span_1234 (b : Fin 75) : a k b*normalRep k 1234 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1234_63 k]
      exact normal_mem k 1303
    · rw [extension_1234_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1234_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1234=0 from arrow_incompatible k b 41 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1234) h]
    exact Submodule.zero_mem _
lemma extension_1235_0 : a k 0*normalRep k 1235=normalRep k 1304 := by
  exact (walk_snoc k 42 [66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1235 (b : Fin 75) : a k b*normalRep k 1235 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1235_0 k]
      exact normal_mem k 1304
  · rw [show a k b*normalRep k 1235=0 from arrow_incompatible k b 42 0 [66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1235) h]
    exact Submodule.zero_mem _
lemma extension_1236_66 : a k 66*normalRep k 1236=normalRep k 1305 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_1236_67 : a k 67*normalRep k 1236=0 := by
  change a k 67*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_977 (a k) (relation_zero k) (e k 42)
lemma extension_1236_68 : a k 68*normalRep k 1236=normalRep k 1306 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_1236 (b : Fin 75) : a k b*normalRep k 1236 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1236_66 k]
      exact normal_mem k 1305
    · rw [extension_1236_67 k]
      exact Submodule.zero_mem _
    · rw [extension_1236_68 k]
      exact normal_mem k 1306
  · rw [show a k b*normalRep k 1236=0 from arrow_incompatible k b 42 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] (normal_endpoints 1236) h]
    exact Submodule.zero_mem _
lemma extension_1237_37 : a k 37*normalRep k 1237=normalRep k 1305 := by
  change a k 37*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1026 (a k) (relation_zero k) (e k 42)
lemma extension_1237_38 : a k 38*normalRep k 1237=normalRep k 1307 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_1237 (b : Fin 75) : a k b*normalRep k 1237 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1237_37 k]
      exact normal_mem k 1305
    · rw [extension_1237_38 k]
      exact normal_mem k 1307
  · rw [show a k b*normalRep k 1237=0 from arrow_incompatible k b 42 29 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] (normal_endpoints 1237) h]
    exact Submodule.zero_mem _
lemma extension_1238_3 : a k 3*normalRep k 1238=(-normalRep k 1306) := by
  change a k 3*walk k 42 [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22]=(-walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_990 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1238 (b : Fin 75) : a k b*normalRep k 1238 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1238_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1306)
  · rw [show a k b*normalRep k 1238=0 from arrow_incompatible k b 42 3 [67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22] (normal_endpoints 1238) h]
    exact Submodule.zero_mem _
lemma extension_1239_30 : a k 30*normalRep k 1239=normalRep k 1308 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1239_31 : a k 31*normalRep k 1239=0 := by
  change a k 31*walk k 43 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_987 (a k) (relation_zero k) (e k 43)
lemma arrow_span_1239 (b : Fin 75) : a k b*normalRep k 1239 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1239_30 k]
      exact normal_mem k 1308
    · rw [extension_1239_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1239=0 from arrow_incompatible k b 43 24 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1239) h]
    exact Submodule.zero_mem _
lemma extension_1240_30 : a k 30*normalRep k 1240=normalRep k 1309 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20] 30).symm
lemma extension_1240_31 : a k 31*normalRep k 1240=0 := by
  change a k 31*walk k 43 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_988 (a k) (relation_zero k) (e k 43)
lemma arrow_span_1240 (b : Fin 75) : a k b*normalRep k 1240 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1240_30 k]
      exact normal_mem k 1309
    · rw [extension_1240_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1240=0 from arrow_incompatible k b 43 24 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20] (normal_endpoints 1240) h]
    exact Submodule.zero_mem _
lemma extension_1241_2 : a k 2*normalRep k 1241=normalRep k 1310 := by
  exact (walk_snoc k 44 [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1241 (b : Fin 75) : a k b*normalRep k 1241 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1241_2 k]
      exact normal_mem k 1310
  · rw [show a k b*normalRep k 1241=0 from arrow_incompatible k b 44 2 [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1241) h]
    exact Submodule.zero_mem _
lemma extension_1242_8 : a k 8*normalRep k 1242=normalRep k 1311 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_1242 (b : Fin 75) : a k b*normalRep k 1242 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1242_8 k]
      exact normal_mem k 1311
  · rw [show a k b*normalRep k 1242=0 from arrow_incompatible k b 44 8 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] (normal_endpoints 1242) h]
    exact Submodule.zero_mem _
lemma extension_1243_72 : a k 72*normalRep k 1243=normalRep k 1312 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] 72).symm
lemma extension_1243_73 : a k 73*normalRep k 1243=normalRep k 1311 := by
  change a k 73*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1024 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1243 (b : Fin 75) : a k b*normalRep k 1243 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1243_72 k]
      exact normal_mem k 1312
    · rw [extension_1243_73 k]
      exact normal_mem k 1311
  · rw [show a k b*normalRep k 1243=0 from arrow_incompatible k b 44 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] (normal_endpoints 1243) h]
    exact Submodule.zero_mem _
lemma extension_1244_22 : a k 22*normalRep k 1244=normalRep k 1313 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] 22).symm
lemma extension_1244_23 : a k 23*normalRep k 1244=normalRep k 1311 := by
  change a k 23*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1025 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1244 (b : Fin 75) : a k b*normalRep k 1244 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1244_22 k]
      exact normal_mem k 1313
    · rw [extension_1244_23 k]
      exact normal_mem k 1311
  · rw [show a k b*normalRep k 1244=0 from arrow_incompatible k b 44 19 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] (normal_endpoints 1244) h]
    exact Submodule.zero_mem _
lemma extension_1245_57 : a k 57*normalRep k 1245=0 := by
  change a k 57*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_995 (a k) (relation_zero k) (e k 45)
lemma extension_1245_58 : a k 58*normalRep k 1245=normalRep k 1314 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27] 58).symm
lemma extension_1245_59 : a k 59*normalRep k 1245=normalRep k 1315 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27] 59).symm
lemma arrow_span_1245 (b : Fin 75) : a k b*normalRep k 1245 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1245_57 k]
      exact Submodule.zero_mem _
    · rw [extension_1245_58 k]
      exact normal_mem k 1314
    · rw [extension_1245_59 k]
      exact normal_mem k 1315
  · rw [show a k b*normalRep k 1245=0 from arrow_incompatible k b 45 39 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27] (normal_endpoints 1245) h]
    exact Submodule.zero_mem _
lemma extension_1246_47 : a k 47*normalRep k 1246=normalRep k 1316 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43] 47).symm
lemma extension_1246_48 : a k 48*normalRep k 1246=normalRep k 1315 := by
  change a k 48*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1002 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1246 (b : Fin 75) : a k b*normalRep k 1246 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1246_47 k]
      exact normal_mem k 1316
    · rw [extension_1246_48 k]
      exact normal_mem k 1315
  · rw [show a k b*normalRep k 1246=0 from arrow_incompatible k b 45 34 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43] (normal_endpoints 1246) h]
    exact Submodule.zero_mem _
lemma extension_1247_6 : a k 6*normalRep k 1247=normalRep k 1316 := by
  change a k 6*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1003 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1247 (b : Fin 75) : a k b*normalRep k 1247 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1247_6 k]
      exact normal_mem k 1316
  · rw [show a k b*normalRep k 1247=0 from arrow_incompatible k b 45 6 [74, 10, 11, 26, 31, 73, 67, 32, 62, 52, 42, 45] (normal_endpoints 1247) h]
    exact Submodule.zero_mem _
lemma arrow_span_1248 (b : Fin 75) : a k b*normalRep k 1248 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1248=0 from arrow_incompatible k b 3 46 [3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2, 0] (normal_endpoints 1248) h]
    exact Submodule.zero_mem _
lemma extension_1249_5 : a k 5*normalRep k 1249=normalRep k 1317 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1249 (b : Fin 75) : a k b*normalRep k 1249 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1249_5 k]
      exact normal_mem k 1317
  · rw [show a k b*normalRep k 1249=0 from arrow_incompatible k b 6 5 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1249) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
