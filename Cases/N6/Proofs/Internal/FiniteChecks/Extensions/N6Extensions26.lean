import N6NormalData
import N6Reduced17
import N6Reduced18
import N6Reduced19
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_1300_9 : a k 9*normalRep k 1300=normalRep k 1363 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1300 (b : Fin 75) : a k b*normalRep k 1300 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1300_9 k]
      exact normal_mem k 1363
  · rw [show a k b*normalRep k 1300=0 from arrow_incompatible k b 40 9 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1300) h]
    exact Submodule.zero_mem _
lemma extension_1301_52 : a k 52*normalRep k 1301=normalRep k 1363 := by
  change a k 52*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1052 (a k) (relation_zero k) (e k 40)
lemma extension_1301_53 : a k 53*normalRep k 1301=normalRep k 1364 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1301 (b : Fin 75) : a k b*normalRep k 1301 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1301_52 k]
      exact normal_mem k 1363
    · rw [extension_1301_53 k]
      exact normal_mem k 1364
  · rw [show a k b*normalRep k 1301=0 from arrow_incompatible k b 40 37 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1301) h]
    exact Submodule.zero_mem _
lemma extension_1302_4 : a k 4*normalRep k 1302=normalRep k 1364 := by
  change a k 4*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1079 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1302 (b : Fin 75) : a k b*normalRep k 1302 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1302_4 k]
      exact normal_mem k 1364
  · rw [show a k b*normalRep k 1302=0 from arrow_incompatible k b 40 4 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1302) h]
    exact Submodule.zero_mem _
lemma extension_1303_20 : a k 20*normalRep k 1303=normalRep k 1365 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1303_21 : a k 21*normalRep k 1303=0 := by
  change a k 21*walk k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1083 (a k) (relation_zero k) (e k 41)
lemma arrow_span_1303 (b : Fin 75) : a k b*normalRep k 1303 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1303_20 k]
      exact normal_mem k 1365
    · rw [extension_1303_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1303=0 from arrow_incompatible k b 41 18 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1303) h]
    exact Submodule.zero_mem _
lemma arrow_span_1304 (b : Fin 75) : a k b*normalRep k 1304 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1304=0 from arrow_incompatible k b 42 46 [66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1304) h]
    exact Submodule.zero_mem _
lemma extension_1305_24 : a k 24*normalRep k 1305=normalRep k 1366 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_1305_25 : a k 25*normalRep k 1305=normalRep k 1367 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_1305 (b : Fin 75) : a k b*normalRep k 1305 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1305_24 k]
      exact normal_mem k 1366
    · rw [extension_1305_25 k]
      exact normal_mem k 1367
  · rw [show a k b*normalRep k 1305=0 from arrow_incompatible k b 42 20 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 1305) h]
    exact Submodule.zero_mem _
lemma extension_1306_39 : a k 39*normalRep k 1306=0 := by
  change a k 39*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1033 (a k) (relation_zero k) (e k 42)
lemma extension_1306_40 : a k 40*normalRep k 1306=(-normalRep k 1367) := by
  change a k 40*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1084 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1306 (b : Fin 75) : a k b*normalRep k 1306 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1306_39 k]
      exact Submodule.zero_mem _
    · rw [extension_1306_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1367)
  · rw [show a k b*normalRep k 1306=0 from arrow_incompatible k b 42 30 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 1306) h]
    exact Submodule.zero_mem _
lemma extension_1307_28 : a k 28*normalRep k 1307=normalRep k 1368 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_1307_29 : a k 29*normalRep k 1307=normalRep k 1366 := by
  change a k 29*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1066 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1307 (b : Fin 75) : a k b*normalRep k 1307 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1307_28 k]
      exact normal_mem k 1368
    · rw [extension_1307_29 k]
      exact normal_mem k 1366
  · rw [show a k b*normalRep k 1307=0 from arrow_incompatible k b 42 23 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 1307) h]
    exact Submodule.zero_mem _
lemma extension_1308_2 : a k 2*normalRep k 1308=normalRep k 1369 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1308 (b : Fin 75) : a k b*normalRep k 1308 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1308_2 k]
      exact normal_mem k 1369
  · rw [show a k b*normalRep k 1308=0 from arrow_incompatible k b 43 2 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1308) h]
    exact Submodule.zero_mem _
lemma extension_1309_2 : a k 2*normalRep k 1309=normalRep k 1370 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30] 2).symm
lemma arrow_span_1309 (b : Fin 75) : a k b*normalRep k 1309 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1309_2 k]
      exact normal_mem k 1370
  · rw [show a k b*normalRep k 1309=0 from arrow_incompatible k b 43 2 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30] (normal_endpoints 1309) h]
    exact Submodule.zero_mem _
lemma extension_1310_0 : a k 0*normalRep k 1310=normalRep k 1371 := by
  exact (walk_snoc k 44 [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1310 (b : Fin 75) : a k b*normalRep k 1310 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1310_0 k]
      exact normal_mem k 1371
  · rw [show a k b*normalRep k 1310=0 from arrow_incompatible k b 44 0 [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1310) h]
    exact Submodule.zero_mem _
lemma extension_1311_66 : a k 66*normalRep k 1311=normalRep k 1372 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_1311_67 : a k 67*normalRep k 1311=0 := by
  change a k 67*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1043 (a k) (relation_zero k) (e k 44)
lemma extension_1311_68 : a k 68*normalRep k 1311=normalRep k 1373 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_1311 (b : Fin 75) : a k b*normalRep k 1311 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1311_66 k]
      exact normal_mem k 1372
    · rw [extension_1311_67 k]
      exact Submodule.zero_mem _
    · rw [extension_1311_68 k]
      exact normal_mem k 1373
  · rw [show a k b*normalRep k 1311=0 from arrow_incompatible k b 44 42 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] (normal_endpoints 1311) h]
    exact Submodule.zero_mem _
lemma extension_1312_37 : a k 37*normalRep k 1312=normalRep k 1372 := by
  change a k 37*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1087 (a k) (relation_zero k) (e k 44)
lemma extension_1312_38 : a k 38*normalRep k 1312=normalRep k 1374 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_1312 (b : Fin 75) : a k b*normalRep k 1312 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1312_37 k]
      exact normal_mem k 1372
    · rw [extension_1312_38 k]
      exact normal_mem k 1374
  · rw [show a k b*normalRep k 1312=0 from arrow_incompatible k b 44 29 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] (normal_endpoints 1312) h]
    exact Submodule.zero_mem _
lemma extension_1313_3 : a k 3*normalRep k 1313=(-normalRep k 1373) := by
  change a k 3*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22]=(-walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1057 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1313 (b : Fin 75) : a k b*normalRep k 1313 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1313_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1373)
  · rw [show a k b*normalRep k 1313=0 from arrow_incompatible k b 44 3 [73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22] (normal_endpoints 1313) h]
    exact Submodule.zero_mem _
lemma extension_1314_33 : a k 33*normalRep k 1314=normalRep k 1375 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58] 33).symm
lemma extension_1314_34 : a k 34*normalRep k 1314=normalRep k 1376 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58] 34).symm
lemma arrow_span_1314 (b : Fin 75) : a k b*normalRep k 1314 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1314_33 k]
      exact normal_mem k 1375
    · rw [extension_1314_34 k]
      exact normal_mem k 1376
  · rw [show a k b*normalRep k 1314=0 from arrow_incompatible k b 45 26 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58] (normal_endpoints 1314) h]
    exact Submodule.zero_mem _
lemma extension_1315_50 : a k 50*normalRep k 1315=normalRep k 1377 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59] 50).symm
lemma extension_1315_51 : a k 51*normalRep k 1315=normalRep k 1376 := by
  change a k 51*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1077 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1315 (b : Fin 75) : a k b*normalRep k 1315 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1315_50 k]
      exact normal_mem k 1377
    · rw [extension_1315_51 k]
      exact normal_mem k 1376
  · rw [show a k b*normalRep k 1315=0 from arrow_incompatible k b 45 36 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59] (normal_endpoints 1315) h]
    exact Submodule.zero_mem _
lemma extension_1316_7 : a k 7*normalRep k 1316=normalRep k 1377 := by
  change a k 7*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1067 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1316 (b : Fin 75) : a k b*normalRep k 1316 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1316_7 k]
      exact normal_mem k 1377
  · rw [show a k b*normalRep k 1316=0 from arrow_incompatible k b 45 7 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 56, 43, 47] (normal_endpoints 1316) h]
    exact Submodule.zero_mem _
lemma extension_1317_63 : a k 63*normalRep k 1317=normalRep k 1378 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1317_64 : a k 64*normalRep k 1317=0 := by
  change a k 64*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1091 (a k) (relation_zero k) (e k 6)
lemma extension_1317_65 : a k 65*normalRep k 1317=0 := by
  change a k 65*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1101 (a k) (relation_zero k) (e k 6)
lemma arrow_span_1317 (b : Fin 75) : a k b*normalRep k 1317 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1317_63 k]
      exact normal_mem k 1378
    · rw [extension_1317_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1317_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1317=0 from arrow_incompatible k b 6 41 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1317) h]
    exact Submodule.zero_mem _
lemma extension_1318_20 : a k 20*normalRep k 1318=normalRep k 1379 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1318_21 : a k 21*normalRep k 1318=0 := by
  change a k 21*walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1134 (a k) (relation_zero k) (e k 7)
lemma arrow_span_1318 (b : Fin 75) : a k b*normalRep k 1318 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1318_20 k]
      exact normal_mem k 1379
    · rw [extension_1318_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1318=0 from arrow_incompatible k b 7 18 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1318) h]
    exact Submodule.zero_mem _
lemma arrow_span_1319 (b : Fin 75) : a k b*normalRep k 1319 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1319=0 from arrow_incompatible k b 8 46 [8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1319) h]
    exact Submodule.zero_mem _
lemma extension_1320_49 : a k 49*normalRep k 1320=normalRep k 1380 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] 49).symm
lemma arrow_span_1320 (b : Fin 75) : a k b*normalRep k 1320 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1320_49 k]
      exact normal_mem k 1380
  · rw [show a k b*normalRep k 1320=0 from arrow_incompatible k b 10 35 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] (normal_endpoints 1320) h]
    exact Submodule.zero_mem _
lemma extension_1321_20 : a k 20*normalRep k 1321=0 := by
  change a k 20*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1109 (a k) (relation_zero k) (e k 10)
lemma extension_1321_21 : a k 21*normalRep k 1321=normalRep k 1381 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] 21).symm
lemma arrow_span_1321 (b : Fin 75) : a k b*normalRep k 1321 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1321_20 k]
      exact Submodule.zero_mem _
    · rw [extension_1321_21 k]
      exact normal_mem k 1381
  · rw [show a k b*normalRep k 1321=0 from arrow_incompatible k b 10 18 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] (normal_endpoints 1321) h]
    exact Submodule.zero_mem _
lemma extension_1322_36 : a k 36*normalRep k 1322=normalRep k 1381 + normalRep k 1380 := by
  change a k 36*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1135 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1322 (b : Fin 75) : a k b*normalRep k 1322 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1322_36 k]
      exact (normalSpan k).add_mem (normal_mem k 1381) (normal_mem k 1380)
  · rw [show a k b*normalRep k 1322=0 from arrow_incompatible k b 10 28 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64] (normal_endpoints 1322) h]
    exact Submodule.zero_mem _
lemma extension_1323_69 : a k 69*normalRep k 1323=normalRep k 1382 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 69).symm
lemma extension_1323_70 : a k 70*normalRep k 1323=0 := by
  change a k 70*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1123 (a k) (relation_zero k) (e k 11)
lemma extension_1323_71 : a k 71*normalRep k 1323=normalRep k 1383 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 71).symm
lemma arrow_span_1323 (b : Fin 75) : a k b*normalRep k 1323 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1323_69 k]
      exact normal_mem k 1382
    · rw [extension_1323_70 k]
      exact Submodule.zero_mem _
    · rw [extension_1323_71 k]
      exact normal_mem k 1383
  · rw [show a k b*normalRep k 1323=0 from arrow_incompatible k b 11 43 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] (normal_endpoints 1323) h]
    exact Submodule.zero_mem _
lemma extension_1324_69 : a k 69*normalRep k 1324=(-normalRep k 1382) := by
  change a k 69*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=(-walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1121 (a k) (relation_zero k) (e k 11)
lemma extension_1324_70 : a k 70*normalRep k 1324=normalRep k 1384 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] 70).symm
lemma extension_1324_71 : a k 71*normalRep k 1324=0 := by
  change a k 71*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1115 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1324 (b : Fin 75) : a k b*normalRep k 1324 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1324_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1382)
    · rw [extension_1324_70 k]
      exact normal_mem k 1384
    · rw [extension_1324_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1324=0 from arrow_incompatible k b 11 43 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] (normal_endpoints 1324) h]
    exact Submodule.zero_mem _
lemma extension_1325_41 : a k 41*normalRep k 1325=normalRep k 1385 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1325_42 : a k 42*normalRep k 1325=0 := by
  change a k 42*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1095 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1325 (b : Fin 75) : a k b*normalRep k 1325 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1325_41 k]
      exact normal_mem k 1385
    · rw [extension_1325_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1325=0 from arrow_incompatible k b 12 31 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1325) h]
    exact Submodule.zero_mem _
lemma extension_1326_54 : a k 54*normalRep k 1326=normalRep k 1386 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1326_55 : a k 55*normalRep k 1326=0 := by
  change a k 55*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1097 (a k) (relation_zero k) (e k 12)
lemma extension_1326_56 : a k 56*normalRep k 1326=normalRep k 1385 := by
  change a k 56*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1125 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1326 (b : Fin 75) : a k b*normalRep k 1326 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1326_54 k]
      exact normal_mem k 1386
    · rw [extension_1326_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1326_56 k]
      exact normal_mem k 1385
  · rw [show a k b*normalRep k 1326=0 from arrow_incompatible k b 12 38 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1326) h]
    exact Submodule.zero_mem _
lemma extension_1327_30 : a k 30*normalRep k 1327=normalRep k 1387 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1327_31 : a k 31*normalRep k 1327=0 := by
  change a k 31*walk k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1112 (a k) (relation_zero k) (e k 13)
lemma arrow_span_1327 (b : Fin 75) : a k b*normalRep k 1327 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1327_30 k]
      exact normal_mem k 1387
    · rw [extension_1327_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1327=0 from arrow_incompatible k b 13 24 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1327) h]
    exact Submodule.zero_mem _
lemma extension_1328_30 : a k 30*normalRep k 1328=normalRep k 1388 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1328_31 : a k 31*normalRep k 1328=0 := by
  change a k 31*walk k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1113 (a k) (relation_zero k) (e k 16)
lemma arrow_span_1328 (b : Fin 75) : a k b*normalRep k 1328 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1328_30 k]
      exact normal_mem k 1388
    · rw [extension_1328_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1328=0 from arrow_incompatible k b 16 24 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1328) h]
    exact Submodule.zero_mem _
lemma extension_1329_2 : a k 2*normalRep k 1329=normalRep k 1389 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1329 (b : Fin 75) : a k b*normalRep k 1329 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1329_2 k]
      exact normal_mem k 1389
  · rw [show a k b*normalRep k 1329=0 from arrow_incompatible k b 18 2 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1329) h]
    exact Submodule.zero_mem _
lemma arrow_span_1330 (b : Fin 75) : a k b*normalRep k 1330 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1330=0 from arrow_incompatible k b 19 46 [22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2, 0] (normal_endpoints 1330) h]
    exact Submodule.zero_mem _
lemma extension_1331_8 : a k 8*normalRep k 1331=normalRep k 1390 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_1331 (b : Fin 75) : a k b*normalRep k 1331 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1331_8 k]
      exact normal_mem k 1390
  · rw [show a k b*normalRep k 1331=0 from arrow_incompatible k b 21 8 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] (normal_endpoints 1331) h]
    exact Submodule.zero_mem _
lemma extension_1332_72 : a k 72*normalRep k 1332=normalRep k 1391 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] 72).symm
lemma extension_1332_73 : a k 73*normalRep k 1332=normalRep k 1390 := by
  change a k 73*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1139 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1332 (b : Fin 75) : a k b*normalRep k 1332 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1332_72 k]
      exact normal_mem k 1391
    · rw [extension_1332_73 k]
      exact normal_mem k 1390
  · rw [show a k b*normalRep k 1332=0 from arrow_incompatible k b 21 44 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] (normal_endpoints 1332) h]
    exact Submodule.zero_mem _
lemma extension_1333_22 : a k 22*normalRep k 1333=normalRep k 1392 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] 22).symm
lemma extension_1333_23 : a k 23*normalRep k 1333=normalRep k 1390 := by
  change a k 23*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1140 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1333 (b : Fin 75) : a k b*normalRep k 1333 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1333_22 k]
      exact normal_mem k 1392
    · rw [extension_1333_23 k]
      exact normal_mem k 1390
  · rw [show a k b*normalRep k 1333=0 from arrow_incompatible k b 21 19 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] (normal_endpoints 1333) h]
    exact Submodule.zero_mem _
lemma extension_1334_5 : a k 5*normalRep k 1334=normalRep k 1393 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1334 (b : Fin 75) : a k b*normalRep k 1334 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1334_5 k]
      exact normal_mem k 1393
  · rw [show a k b*normalRep k 1334=0 from arrow_incompatible k b 22 5 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1334) h]
    exact Submodule.zero_mem _
lemma extension_1335_33 : a k 33*normalRep k 1335=0 := by
  change a k 33*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1088 (a k) (relation_zero k) (e k 22)
lemma extension_1335_34 : a k 34*normalRep k 1335=normalRep k 1393 := by
  change a k 34*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1129 (a k) (relation_zero k) (e k 22)
lemma arrow_span_1335 (b : Fin 75) : a k b*normalRep k 1335 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1335_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1335_34 k]
      exact normal_mem k 1393
  · rw [show a k b*normalRep k 1335=0 from arrow_incompatible k b 22 26 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1335) h]
    exact Submodule.zero_mem _
lemma extension_1336_66 : a k 66*normalRep k 1336=normalRep k 1394 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_1336_67 : a k 67*normalRep k 1336=0 := by
  change a k 67*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1104 (a k) (relation_zero k) (e k 24)
lemma extension_1336_68 : a k 68*normalRep k 1336=normalRep k 1395 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_1336 (b : Fin 75) : a k b*normalRep k 1336 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1336_66 k]
      exact normal_mem k 1394
    · rw [extension_1336_67 k]
      exact Submodule.zero_mem _
    · rw [extension_1336_68 k]
      exact normal_mem k 1395
  · rw [show a k b*normalRep k 1336=0 from arrow_incompatible k b 24 42 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] (normal_endpoints 1336) h]
    exact Submodule.zero_mem _
lemma extension_1337_37 : a k 37*normalRep k 1337=normalRep k 1394 := by
  change a k 37*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1141 (a k) (relation_zero k) (e k 24)
lemma extension_1337_38 : a k 38*normalRep k 1337=normalRep k 1396 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_1337 (b : Fin 75) : a k b*normalRep k 1337 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1337_37 k]
      exact normal_mem k 1394
    · rw [extension_1337_38 k]
      exact normal_mem k 1396
  · rw [show a k b*normalRep k 1337=0 from arrow_incompatible k b 24 29 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] (normal_endpoints 1337) h]
    exact Submodule.zero_mem _
lemma extension_1338_3 : a k 3*normalRep k 1338=(-normalRep k 1395) := by
  change a k 3*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22]=(-walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1116 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1338 (b : Fin 75) : a k b*normalRep k 1338 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1338_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1395)
  · rw [show a k b*normalRep k 1338=0 from arrow_incompatible k b 24 3 [31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22] (normal_endpoints 1338) h]
    exact Submodule.zero_mem _
lemma extension_1339_9 : a k 9*normalRep k 1339=normalRep k 1397 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1339 (b : Fin 75) : a k b*normalRep k 1339 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1339_9 k]
      exact normal_mem k 1397
  · rw [show a k b*normalRep k 1339=0 from arrow_incompatible k b 25 9 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1339) h]
    exact Submodule.zero_mem _
lemma extension_1340_52 : a k 52*normalRep k 1340=normalRep k 1397 := by
  change a k 52*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1110 (a k) (relation_zero k) (e k 25)
lemma extension_1340_53 : a k 53*normalRep k 1340=normalRep k 1398 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1340 (b : Fin 75) : a k b*normalRep k 1340 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1340_52 k]
      exact normal_mem k 1397
    · rw [extension_1340_53 k]
      exact normal_mem k 1398
  · rw [show a k b*normalRep k 1340=0 from arrow_incompatible k b 25 37 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1340) h]
    exact Submodule.zero_mem _
lemma extension_1341_4 : a k 4*normalRep k 1341=normalRep k 1398 := by
  change a k 4*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1132 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1341 (b : Fin 75) : a k b*normalRep k 1341 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1341_4 k]
      exact normal_mem k 1398
  · rw [show a k b*normalRep k 1341=0 from arrow_incompatible k b 25 4 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1341) h]
    exact Submodule.zero_mem _
lemma extension_1342_20 : a k 20*normalRep k 1342=normalRep k 1399 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1342_21 : a k 21*normalRep k 1342=0 := by
  change a k 21*walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1136 (a k) (relation_zero k) (e k 26)
lemma arrow_span_1342 (b : Fin 75) : a k b*normalRep k 1342 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1342_20 k]
      exact normal_mem k 1399
    · rw [extension_1342_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1342=0 from arrow_incompatible k b 26 18 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1342) h]
    exact Submodule.zero_mem _
lemma extension_1343_43 : a k 43*normalRep k 1343=0 := by
  change a k 43*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1099 (a k) (relation_zero k) (e k 27)
lemma extension_1343_44 : a k 44*normalRep k 1343=normalRep k 1400 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1343 (b : Fin 75) : a k b*normalRep k 1343 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1343_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1343_44 k]
      exact normal_mem k 1400
  · rw [show a k b*normalRep k 1343=0 from arrow_incompatible k b 27 32 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1343) h]
    exact Submodule.zero_mem _
lemma extension_1344_15 : a k 15*normalRep k 1344=normalRep k 1401 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1344_16 : a k 16*normalRep k 1344=normalRep k 1400 := by
  change a k 16*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1127 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1344 (b : Fin 75) : a k b*normalRep k 1344 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1344_15 k]
      exact normal_mem k 1401
    · rw [extension_1344_16 k]
      exact normal_mem k 1400
  · rw [show a k b*normalRep k 1344=0 from arrow_incompatible k b 27 15 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1344) h]
    exact Submodule.zero_mem _
lemma extension_1345_2 : a k 2*normalRep k 1345=normalRep k 1402 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30] 2).symm
lemma arrow_span_1345 (b : Fin 75) : a k b*normalRep k 1345 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1345_2 k]
      exact normal_mem k 1402
  · rw [show a k b*normalRep k 1345=0 from arrow_incompatible k b 28 2 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30] (normal_endpoints 1345) h]
    exact Submodule.zero_mem _
lemma extension_1346_9 : a k 9*normalRep k 1346=normalRep k 1403 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1346 (b : Fin 75) : a k b*normalRep k 1346 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1346_9 k]
      exact normal_mem k 1403
  · rw [show a k b*normalRep k 1346=0 from arrow_incompatible k b 30 9 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1346) h]
    exact Submodule.zero_mem _
lemma extension_1347_52 : a k 52*normalRep k 1347=normalRep k 1403 := by
  change a k 52*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1111 (a k) (relation_zero k) (e k 30)
lemma extension_1347_53 : a k 53*normalRep k 1347=normalRep k 1404 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1347 (b : Fin 75) : a k b*normalRep k 1347 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1347_52 k]
      exact normal_mem k 1403
    · rw [extension_1347_53 k]
      exact normal_mem k 1404
  · rw [show a k b*normalRep k 1347=0 from arrow_incompatible k b 30 37 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1347) h]
    exact Submodule.zero_mem _
lemma extension_1348_4 : a k 4*normalRep k 1348=normalRep k 1404 := by
  change a k 4*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1133 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1348 (b : Fin 75) : a k b*normalRep k 1348 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1348_4 k]
      exact normal_mem k 1404
  · rw [show a k b*normalRep k 1348=0 from arrow_incompatible k b 30 4 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1348) h]
    exact Submodule.zero_mem _
lemma extension_1349_57 : a k 57*normalRep k 1349=normalRep k 1405 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1349_58 : a k 58*normalRep k 1349=normalRep k 1406 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1349_59 : a k 59*normalRep k 1349=0 := by
  change a k 59*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1107 (a k) (relation_zero k) (e k 31)
lemma arrow_span_1349 (b : Fin 75) : a k b*normalRep k 1349 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1349_57 k]
      exact normal_mem k 1405
    · rw [extension_1349_58 k]
      exact normal_mem k 1406
    · rw [extension_1349_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1349=0 from arrow_incompatible k b 31 39 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1349) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
