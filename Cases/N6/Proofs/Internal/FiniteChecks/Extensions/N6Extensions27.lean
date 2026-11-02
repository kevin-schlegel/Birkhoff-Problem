import N6NormalData
import N6Reduced18
import N6Reduced19
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_1350_1 : a k 1*normalRep k 1350=normalRep k 1406 := by
  change a k 1*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1105 (a k) (relation_zero k) (e k 31)
lemma arrow_span_1350 (b : Fin 75) : a k b*normalRep k 1350 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1350_1 k]
      exact normal_mem k 1406
  · rw [show a k b*normalRep k 1350=0 from arrow_incompatible k b 31 1 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1350) h]
    exact Submodule.zero_mem _
lemma extension_1351_5 : a k 5*normalRep k 1351=normalRep k 1407 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1351 (b : Fin 75) : a k b*normalRep k 1351 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1351_5 k]
      exact normal_mem k 1407
  · rw [show a k b*normalRep k 1351=0 from arrow_incompatible k b 32 5 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1351) h]
    exact Submodule.zero_mem _
lemma extension_1352_33 : a k 33*normalRep k 1352=0 := by
  change a k 33*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1089 (a k) (relation_zero k) (e k 32)
lemma extension_1352_34 : a k 34*normalRep k 1352=normalRep k 1407 := by
  change a k 34*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1130 (a k) (relation_zero k) (e k 32)
lemma arrow_span_1352 (b : Fin 75) : a k b*normalRep k 1352 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1352_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1352_34 k]
      exact normal_mem k 1407
  · rw [show a k b*normalRep k 1352=0 from arrow_incompatible k b 32 26 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1352) h]
    exact Submodule.zero_mem _
lemma extension_1353_5 : a k 5*normalRep k 1353=normalRep k 1408 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1353 (b : Fin 75) : a k b*normalRep k 1353 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1353_5 k]
      exact normal_mem k 1408
  · rw [show a k b*normalRep k 1353=0 from arrow_incompatible k b 33 5 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1353) h]
    exact Submodule.zero_mem _
lemma extension_1354_33 : a k 33*normalRep k 1354=0 := by
  change a k 33*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1090 (a k) (relation_zero k) (e k 33)
lemma extension_1354_34 : a k 34*normalRep k 1354=normalRep k 1408 := by
  change a k 34*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1131 (a k) (relation_zero k) (e k 33)
lemma arrow_span_1354 (b : Fin 75) : a k b*normalRep k 1354 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1354_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1354_34 k]
      exact normal_mem k 1408
  · rw [show a k b*normalRep k 1354=0 from arrow_incompatible k b 33 26 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1354) h]
    exact Submodule.zero_mem _
lemma extension_1355_63 : a k 63*normalRep k 1355=normalRep k 1409 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1355_64 : a k 64*normalRep k 1355=0 := by
  change a k 64*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1092 (a k) (relation_zero k) (e k 34)
lemma extension_1355_65 : a k 65*normalRep k 1355=0 := by
  change a k 65*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1102 (a k) (relation_zero k) (e k 34)
lemma arrow_span_1355 (b : Fin 75) : a k b*normalRep k 1355 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1355_63 k]
      exact normal_mem k 1409
    · rw [extension_1355_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1355_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1355=0 from arrow_incompatible k b 34 41 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1355) h]
    exact Submodule.zero_mem _
lemma extension_1356_2 : a k 2*normalRep k 1356=normalRep k 1410 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1356 (b : Fin 75) : a k b*normalRep k 1356 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1356_2 k]
      exact normal_mem k 1410
  · rw [show a k b*normalRep k 1356=0 from arrow_incompatible k b 35 2 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1356) h]
    exact Submodule.zero_mem _
lemma extension_1357_20 : a k 20*normalRep k 1357=normalRep k 1411 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1357_21 : a k 21*normalRep k 1357=0 := by
  change a k 21*walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1137 (a k) (relation_zero k) (e k 36)
lemma arrow_span_1357 (b : Fin 75) : a k b*normalRep k 1357 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1357_20 k]
      exact normal_mem k 1411
    · rw [extension_1357_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1357=0 from arrow_incompatible k b 36 18 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1357) h]
    exact Submodule.zero_mem _
lemma extension_1358_43 : a k 43*normalRep k 1358=0 := by
  change a k 43*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1100 (a k) (relation_zero k) (e k 37)
lemma extension_1358_44 : a k 44*normalRep k 1358=normalRep k 1412 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1358 (b : Fin 75) : a k b*normalRep k 1358 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1358_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1358_44 k]
      exact normal_mem k 1412
  · rw [show a k b*normalRep k 1358=0 from arrow_incompatible k b 37 32 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1358) h]
    exact Submodule.zero_mem _
lemma extension_1359_15 : a k 15*normalRep k 1359=normalRep k 1413 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1359_16 : a k 16*normalRep k 1359=normalRep k 1412 := by
  change a k 16*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54]=walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1128 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1359 (b : Fin 75) : a k b*normalRep k 1359 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1359_15 k]
      exact normal_mem k 1413
    · rw [extension_1359_16 k]
      exact normal_mem k 1412
  · rw [show a k b*normalRep k 1359=0 from arrow_incompatible k b 37 15 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1359) h]
    exact Submodule.zero_mem _
lemma extension_1360_57 : a k 57*normalRep k 1360=normalRep k 1414 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1360_58 : a k 58*normalRep k 1360=normalRep k 1415 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1360_59 : a k 59*normalRep k 1360=0 := by
  change a k 59*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1108 (a k) (relation_zero k) (e k 38)
lemma arrow_span_1360 (b : Fin 75) : a k b*normalRep k 1360 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1360_57 k]
      exact normal_mem k 1414
    · rw [extension_1360_58 k]
      exact normal_mem k 1415
    · rw [extension_1360_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1360=0 from arrow_incompatible k b 38 39 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1360) h]
    exact Submodule.zero_mem _
lemma extension_1361_1 : a k 1*normalRep k 1361=normalRep k 1415 := by
  change a k 1*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1106 (a k) (relation_zero k) (e k 38)
lemma arrow_span_1361 (b : Fin 75) : a k b*normalRep k 1361 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1361_1 k]
      exact normal_mem k 1415
  · rw [show a k b*normalRep k 1361=0 from arrow_incompatible k b 38 1 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1361) h]
    exact Submodule.zero_mem _
lemma extension_1362_63 : a k 63*normalRep k 1362=normalRep k 1416 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1362_64 : a k 64*normalRep k 1362=0 := by
  change a k 64*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1093 (a k) (relation_zero k) (e k 39)
lemma extension_1362_65 : a k 65*normalRep k 1362=0 := by
  change a k 65*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1103 (a k) (relation_zero k) (e k 39)
lemma arrow_span_1362 (b : Fin 75) : a k b*normalRep k 1362 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1362_63 k]
      exact normal_mem k 1416
    · rw [extension_1362_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1362_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1362=0 from arrow_incompatible k b 39 41 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1362) h]
    exact Submodule.zero_mem _
lemma extension_1363_41 : a k 41*normalRep k 1363=normalRep k 1417 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1363_42 : a k 42*normalRep k 1363=0 := by
  change a k 42*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1096 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1363 (b : Fin 75) : a k b*normalRep k 1363 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1363_41 k]
      exact normal_mem k 1417
    · rw [extension_1363_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1363=0 from arrow_incompatible k b 40 31 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1363) h]
    exact Submodule.zero_mem _
lemma extension_1364_54 : a k 54*normalRep k 1364=normalRep k 1418 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1364_55 : a k 55*normalRep k 1364=0 := by
  change a k 55*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1098 (a k) (relation_zero k) (e k 40)
lemma extension_1364_56 : a k 56*normalRep k 1364=normalRep k 1417 := by
  change a k 56*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1126 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1364 (b : Fin 75) : a k b*normalRep k 1364 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1364_54 k]
      exact normal_mem k 1418
    · rw [extension_1364_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1364_56 k]
      exact normal_mem k 1417
  · rw [show a k b*normalRep k 1364=0 from arrow_incompatible k b 40 38 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1364) h]
    exact Submodule.zero_mem _
lemma extension_1365_30 : a k 30*normalRep k 1365=normalRep k 1419 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1365_31 : a k 31*normalRep k 1365=0 := by
  change a k 31*walk k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1114 (a k) (relation_zero k) (e k 41)
lemma arrow_span_1365 (b : Fin 75) : a k b*normalRep k 1365 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1365_30 k]
      exact normal_mem k 1419
    · rw [extension_1365_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1365=0 from arrow_incompatible k b 41 24 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1365) h]
    exact Submodule.zero_mem _
lemma extension_1366_18 : a k 18*normalRep k 1366=normalRep k 1420 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_1366_19 : a k 19*normalRep k 1366=normalRep k 1421 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_1366 (b : Fin 75) : a k b*normalRep k 1366 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1366_18 k]
      exact normal_mem k 1420
    · rw [extension_1366_19 k]
      exact normal_mem k 1421
  · rw [show a k b*normalRep k 1366=0 from arrow_incompatible k b 42 17 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 1366) h]
    exact Submodule.zero_mem _
lemma extension_1367_60 : a k 60*normalRep k 1367=normalRep k 1422 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_1367_61 : a k 61*normalRep k 1367=0 := by
  change a k 61*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1117 (a k) (relation_zero k) (e k 42)
lemma extension_1367_62 : a k 62*normalRep k 1367=normalRep k 1421 := by
  change a k 62*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1118 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1367 (b : Fin 75) : a k b*normalRep k 1367 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1367_60 k]
      exact normal_mem k 1422
    · rw [extension_1367_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1367_62 k]
      exact normal_mem k 1421
  · rw [show a k b*normalRep k 1367=0 from arrow_incompatible k b 42 40 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 1367) h]
    exact Submodule.zero_mem _
lemma extension_1368_14 : a k 14*normalRep k 1368=normalRep k 1420 := by
  change a k 14*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1119 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1368 (b : Fin 75) : a k b*normalRep k 1368 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1368_14 k]
      exact normal_mem k 1420
  · rw [show a k b*normalRep k 1368=0 from arrow_incompatible k b 42 14 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 1368) h]
    exact Submodule.zero_mem _
lemma extension_1369_0 : a k 0*normalRep k 1369=normalRep k 1423 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1369 (b : Fin 75) : a k b*normalRep k 1369 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1369_0 k]
      exact normal_mem k 1423
  · rw [show a k b*normalRep k 1369=0 from arrow_incompatible k b 43 0 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1369) h]
    exact Submodule.zero_mem _
lemma extension_1370_0 : a k 0*normalRep k 1370=normalRep k 1424 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2] 0).symm
lemma arrow_span_1370 (b : Fin 75) : a k b*normalRep k 1370 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1370_0 k]
      exact normal_mem k 1424
  · rw [show a k b*normalRep k 1370=0 from arrow_incompatible k b 43 0 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2] (normal_endpoints 1370) h]
    exact Submodule.zero_mem _
lemma arrow_span_1371 (b : Fin 75) : a k b*normalRep k 1371 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1371=0 from arrow_incompatible k b 44 46 [72, 37, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1371) h]
    exact Submodule.zero_mem _
lemma extension_1372_24 : a k 24*normalRep k 1372=normalRep k 1425 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_1372_25 : a k 25*normalRep k 1372=normalRep k 1426 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_1372 (b : Fin 75) : a k b*normalRep k 1372 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1372_24 k]
      exact normal_mem k 1425
    · rw [extension_1372_25 k]
      exact normal_mem k 1426
  · rw [show a k b*normalRep k 1372=0 from arrow_incompatible k b 44 20 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 1372) h]
    exact Submodule.zero_mem _
lemma extension_1373_39 : a k 39*normalRep k 1373=0 := by
  change a k 39*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1094 (a k) (relation_zero k) (e k 44)
lemma extension_1373_40 : a k 40*normalRep k 1373=(-normalRep k 1426) := by
  change a k 40*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1138 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1373 (b : Fin 75) : a k b*normalRep k 1373 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1373_39 k]
      exact Submodule.zero_mem _
    · rw [extension_1373_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1426)
  · rw [show a k b*normalRep k 1373=0 from arrow_incompatible k b 44 30 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 1373) h]
    exact Submodule.zero_mem _
lemma extension_1374_28 : a k 28*normalRep k 1374=normalRep k 1427 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_1374_29 : a k 29*normalRep k 1374=normalRep k 1425 := by
  change a k 29*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1122 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1374 (b : Fin 75) : a k b*normalRep k 1374 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1374_28 k]
      exact normal_mem k 1427
    · rw [extension_1374_29 k]
      exact normal_mem k 1425
  · rw [show a k b*normalRep k 1374=0 from arrow_incompatible k b 44 23 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 1374) h]
    exact Submodule.zero_mem _
lemma extension_1375_13 : a k 13*normalRep k 1375=normalRep k 1428 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33] 13).symm
lemma arrow_span_1375 (b : Fin 75) : a k b*normalRep k 1375 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1375_13 k]
      exact normal_mem k 1428
  · rw [show a k b*normalRep k 1375=0 from arrow_incompatible k b 45 13 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33] (normal_endpoints 1375) h]
    exact Submodule.zero_mem _
lemma extension_1376_63 : a k 63*normalRep k 1376=normalRep k 1429 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] 63).symm
lemma extension_1376_64 : a k 64*normalRep k 1376=normalRep k 1430 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] 64).symm
lemma extension_1376_65 : a k 65*normalRep k 1376=normalRep k 1428 := by
  change a k 65*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1120 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1376 (b : Fin 75) : a k b*normalRep k 1376 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1376_63 k]
      exact normal_mem k 1429
    · rw [extension_1376_64 k]
      exact normal_mem k 1430
    · rw [extension_1376_65 k]
      exact normal_mem k 1428
  · rw [show a k b*normalRep k 1376=0 from arrow_incompatible k b 45 41 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34] (normal_endpoints 1376) h]
    exact Submodule.zero_mem _
lemma extension_1377_17 : a k 17*normalRep k 1377=normalRep k 1429 := by
  change a k 17*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1124 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1377 (b : Fin 75) : a k b*normalRep k 1377 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1377_17 k]
      exact normal_mem k 1429
  · rw [show a k b*normalRep k 1377=0 from arrow_incompatible k b 45 16 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 59, 50] (normal_endpoints 1377) h]
    exact Submodule.zero_mem _
lemma extension_1378_20 : a k 20*normalRep k 1378=normalRep k 1431 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1378_21 : a k 21*normalRep k 1378=0 := by
  change a k 21*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1182 (a k) (relation_zero k) (e k 6)
lemma arrow_span_1378 (b : Fin 75) : a k b*normalRep k 1378 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1378_20 k]
      exact normal_mem k 1431
    · rw [extension_1378_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1378=0 from arrow_incompatible k b 6 18 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1378) h]
    exact Submodule.zero_mem _
lemma extension_1379_30 : a k 30*normalRep k 1379=normalRep k 1432 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1379_31 : a k 31*normalRep k 1379=0 := by
  change a k 31*walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1164 (a k) (relation_zero k) (e k 7)
lemma arrow_span_1379 (b : Fin 75) : a k b*normalRep k 1379 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1379_30 k]
      exact normal_mem k 1432
    · rw [extension_1379_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1379=0 from arrow_incompatible k b 7 24 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1379) h]
    exact Submodule.zero_mem _
lemma extension_1380_69 : a k 69*normalRep k 1380=normalRep k 1433 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 69).symm
lemma extension_1380_70 : a k 70*normalRep k 1380=0 := by
  change a k 70*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1174 (a k) (relation_zero k) (e k 10)
lemma extension_1380_71 : a k 71*normalRep k 1380=normalRep k 1434 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 71).symm
lemma arrow_span_1380 (b : Fin 75) : a k b*normalRep k 1380 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1380_69 k]
      exact normal_mem k 1433
    · rw [extension_1380_70 k]
      exact Submodule.zero_mem _
    · rw [extension_1380_71 k]
      exact normal_mem k 1434
  · rw [show a k b*normalRep k 1380=0 from arrow_incompatible k b 10 43 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] (normal_endpoints 1380) h]
    exact Submodule.zero_mem _
lemma extension_1381_69 : a k 69*normalRep k 1381=(-normalRep k 1433) := by
  change a k 69*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=(-walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1172 (a k) (relation_zero k) (e k 10)
lemma extension_1381_70 : a k 70*normalRep k 1381=normalRep k 1435 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] 70).symm
lemma extension_1381_71 : a k 71*normalRep k 1381=0 := by
  change a k 71*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1167 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1381 (b : Fin 75) : a k b*normalRep k 1381 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1381_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1433)
    · rw [extension_1381_70 k]
      exact normal_mem k 1435
    · rw [extension_1381_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1381=0 from arrow_incompatible k b 10 43 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] (normal_endpoints 1381) h]
    exact Submodule.zero_mem _
lemma extension_1382_8 : a k 8*normalRep k 1382=normalRep k 1436 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_1382 (b : Fin 75) : a k b*normalRep k 1382 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1382_8 k]
      exact normal_mem k 1436
  · rw [show a k b*normalRep k 1382=0 from arrow_incompatible k b 11 8 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] (normal_endpoints 1382) h]
    exact Submodule.zero_mem _
lemma extension_1383_72 : a k 72*normalRep k 1383=normalRep k 1437 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] 72).symm
lemma extension_1383_73 : a k 73*normalRep k 1383=normalRep k 1436 := by
  change a k 73*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1187 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1383 (b : Fin 75) : a k b*normalRep k 1383 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1383_72 k]
      exact normal_mem k 1437
    · rw [extension_1383_73 k]
      exact normal_mem k 1436
  · rw [show a k b*normalRep k 1383=0 from arrow_incompatible k b 11 44 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] (normal_endpoints 1383) h]
    exact Submodule.zero_mem _
lemma extension_1384_22 : a k 22*normalRep k 1384=normalRep k 1438 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] 22).symm
lemma extension_1384_23 : a k 23*normalRep k 1384=normalRep k 1436 := by
  change a k 23*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1188 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1384 (b : Fin 75) : a k b*normalRep k 1384 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1384_22 k]
      exact normal_mem k 1438
    · rw [extension_1384_23 k]
      exact normal_mem k 1436
  · rw [show a k b*normalRep k 1384=0 from arrow_incompatible k b 11 19 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] (normal_endpoints 1384) h]
    exact Submodule.zero_mem _
lemma extension_1385_43 : a k 43*normalRep k 1385=0 := by
  change a k 43*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1152 (a k) (relation_zero k) (e k 12)
lemma extension_1385_44 : a k 44*normalRep k 1385=normalRep k 1439 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1385 (b : Fin 75) : a k b*normalRep k 1385 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1385_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1385_44 k]
      exact normal_mem k 1439
  · rw [show a k b*normalRep k 1385=0 from arrow_incompatible k b 12 32 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1385) h]
    exact Submodule.zero_mem _
lemma extension_1386_15 : a k 15*normalRep k 1386=normalRep k 1440 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1386_16 : a k 16*normalRep k 1386=normalRep k 1439 := by
  change a k 16*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1177 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1386 (b : Fin 75) : a k b*normalRep k 1386 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1386_15 k]
      exact normal_mem k 1440
    · rw [extension_1386_16 k]
      exact normal_mem k 1439
  · rw [show a k b*normalRep k 1386=0 from arrow_incompatible k b 12 15 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1386) h]
    exact Submodule.zero_mem _
lemma extension_1387_2 : a k 2*normalRep k 1387=normalRep k 1441 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1387 (b : Fin 75) : a k b*normalRep k 1387 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1387_2 k]
      exact normal_mem k 1441
  · rw [show a k b*normalRep k 1387=0 from arrow_incompatible k b 13 2 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1387) h]
    exact Submodule.zero_mem _
lemma extension_1388_2 : a k 2*normalRep k 1388=normalRep k 1442 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1388 (b : Fin 75) : a k b*normalRep k 1388 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1388_2 k]
      exact normal_mem k 1442
  · rw [show a k b*normalRep k 1388=0 from arrow_incompatible k b 16 2 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1388) h]
    exact Submodule.zero_mem _
lemma extension_1389_0 : a k 0*normalRep k 1389=normalRep k 1443 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1389 (b : Fin 75) : a k b*normalRep k 1389 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1389_0 k]
      exact normal_mem k 1443
  · rw [show a k b*normalRep k 1389=0 from arrow_incompatible k b 18 0 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1389) h]
    exact Submodule.zero_mem _
lemma extension_1390_66 : a k 66*normalRep k 1390=normalRep k 1444 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_1390_67 : a k 67*normalRep k 1390=0 := by
  change a k 67*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1157 (a k) (relation_zero k) (e k 21)
lemma extension_1390_68 : a k 68*normalRep k 1390=normalRep k 1445 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_1390 (b : Fin 75) : a k b*normalRep k 1390 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1390_66 k]
      exact normal_mem k 1444
    · rw [extension_1390_67 k]
      exact Submodule.zero_mem _
    · rw [extension_1390_68 k]
      exact normal_mem k 1445
  · rw [show a k b*normalRep k 1390=0 from arrow_incompatible k b 21 42 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] (normal_endpoints 1390) h]
    exact Submodule.zero_mem _
lemma extension_1391_37 : a k 37*normalRep k 1391=normalRep k 1444 := by
  change a k 37*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1189 (a k) (relation_zero k) (e k 21)
lemma extension_1391_38 : a k 38*normalRep k 1391=normalRep k 1446 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_1391 (b : Fin 75) : a k b*normalRep k 1391 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1391_37 k]
      exact normal_mem k 1444
    · rw [extension_1391_38 k]
      exact normal_mem k 1446
  · rw [show a k b*normalRep k 1391=0 from arrow_incompatible k b 21 29 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] (normal_endpoints 1391) h]
    exact Submodule.zero_mem _
lemma extension_1392_3 : a k 3*normalRep k 1392=(-normalRep k 1445) := by
  change a k 3*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22]=(-walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1168 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1392 (b : Fin 75) : a k b*normalRep k 1392 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1392_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1445)
  · rw [show a k b*normalRep k 1392=0 from arrow_incompatible k b 21 3 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22] (normal_endpoints 1392) h]
    exact Submodule.zero_mem _
lemma extension_1393_63 : a k 63*normalRep k 1393=normalRep k 1447 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1393_64 : a k 64*normalRep k 1393=0 := by
  change a k 64*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1144 (a k) (relation_zero k) (e k 22)
lemma extension_1393_65 : a k 65*normalRep k 1393=0 := by
  change a k 65*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1154 (a k) (relation_zero k) (e k 22)
lemma arrow_span_1393 (b : Fin 75) : a k b*normalRep k 1393 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1393_63 k]
      exact normal_mem k 1447
    · rw [extension_1393_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1393_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1393=0 from arrow_incompatible k b 22 41 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1393) h]
    exact Submodule.zero_mem _
lemma extension_1394_24 : a k 24*normalRep k 1394=normalRep k 1448 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_1394_25 : a k 25*normalRep k 1394=normalRep k 1449 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_1394 (b : Fin 75) : a k b*normalRep k 1394 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1394_24 k]
      exact normal_mem k 1448
    · rw [extension_1394_25 k]
      exact normal_mem k 1449
  · rw [show a k b*normalRep k 1394=0 from arrow_incompatible k b 24 20 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 1394) h]
    exact Submodule.zero_mem _
lemma extension_1395_39 : a k 39*normalRep k 1395=0 := by
  change a k 39*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1147 (a k) (relation_zero k) (e k 24)
lemma extension_1395_40 : a k 40*normalRep k 1395=(-normalRep k 1449) := by
  change a k 40*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1186 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1395 (b : Fin 75) : a k b*normalRep k 1395 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1395_39 k]
      exact Submodule.zero_mem _
    · rw [extension_1395_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1449)
  · rw [show a k b*normalRep k 1395=0 from arrow_incompatible k b 24 30 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 1395) h]
    exact Submodule.zero_mem _
lemma extension_1396_28 : a k 28*normalRep k 1396=normalRep k 1450 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_1396_29 : a k 29*normalRep k 1396=normalRep k 1448 := by
  change a k 29*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1173 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1396 (b : Fin 75) : a k b*normalRep k 1396 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1396_28 k]
      exact normal_mem k 1450
    · rw [extension_1396_29 k]
      exact normal_mem k 1448
  · rw [show a k b*normalRep k 1396=0 from arrow_incompatible k b 24 23 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 1396) h]
    exact Submodule.zero_mem _
lemma extension_1397_41 : a k 41*normalRep k 1397=normalRep k 1451 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1397_42 : a k 42*normalRep k 1397=0 := by
  change a k 42*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1148 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1397 (b : Fin 75) : a k b*normalRep k 1397 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1397_41 k]
      exact normal_mem k 1451
    · rw [extension_1397_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1397=0 from arrow_incompatible k b 25 31 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1397) h]
    exact Submodule.zero_mem _
lemma extension_1398_54 : a k 54*normalRep k 1398=normalRep k 1452 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1398_55 : a k 55*normalRep k 1398=0 := by
  change a k 55*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1150 (a k) (relation_zero k) (e k 25)
lemma extension_1398_56 : a k 56*normalRep k 1398=normalRep k 1451 := by
  change a k 56*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1175 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1398 (b : Fin 75) : a k b*normalRep k 1398 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1398_54 k]
      exact normal_mem k 1452
    · rw [extension_1398_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1398_56 k]
      exact normal_mem k 1451
  · rw [show a k b*normalRep k 1398=0 from arrow_incompatible k b 25 38 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1398) h]
    exact Submodule.zero_mem _
lemma extension_1399_30 : a k 30*normalRep k 1399=normalRep k 1453 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1399_31 : a k 31*normalRep k 1399=0 := by
  change a k 31*walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1165 (a k) (relation_zero k) (e k 26)
lemma arrow_span_1399 (b : Fin 75) : a k b*normalRep k 1399 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1399_30 k]
      exact normal_mem k 1453
    · rw [extension_1399_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1399=0 from arrow_incompatible k b 26 24 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1399) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
