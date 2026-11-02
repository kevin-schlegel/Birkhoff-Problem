import N6NormalData
import N6Reduced19
import N6Reduced20
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_1400_57 : a k 57*normalRep k 1400=normalRep k 1454 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1400_58 : a k 58*normalRep k 1400=normalRep k 1455 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1400_59 : a k 59*normalRep k 1400=0 := by
  change a k 59*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1160 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1400 (b : Fin 75) : a k b*normalRep k 1400 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1400_57 k]
      exact normal_mem k 1454
    · rw [extension_1400_58 k]
      exact normal_mem k 1455
    · rw [extension_1400_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1400=0 from arrow_incompatible k b 27 39 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1400) h]
    exact Submodule.zero_mem _
lemma extension_1401_1 : a k 1*normalRep k 1401=normalRep k 1455 := by
  change a k 1*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1158 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1401 (b : Fin 75) : a k b*normalRep k 1401 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1401_1 k]
      exact normal_mem k 1455
  · rw [show a k b*normalRep k 1401=0 from arrow_incompatible k b 27 1 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1401) h]
    exact Submodule.zero_mem _
lemma extension_1402_0 : a k 0*normalRep k 1402=normalRep k 1456 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2] 0).symm
lemma arrow_span_1402 (b : Fin 75) : a k b*normalRep k 1402 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1402_0 k]
      exact normal_mem k 1456
  · rw [show a k b*normalRep k 1402=0 from arrow_incompatible k b 28 0 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2] (normal_endpoints 1402) h]
    exact Submodule.zero_mem _
lemma extension_1403_41 : a k 41*normalRep k 1403=normalRep k 1457 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1403_42 : a k 42*normalRep k 1403=0 := by
  change a k 42*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1149 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1403 (b : Fin 75) : a k b*normalRep k 1403 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1403_41 k]
      exact normal_mem k 1457
    · rw [extension_1403_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1403=0 from arrow_incompatible k b 30 31 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1403) h]
    exact Submodule.zero_mem _
lemma extension_1404_54 : a k 54*normalRep k 1404=normalRep k 1458 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1404_55 : a k 55*normalRep k 1404=0 := by
  change a k 55*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1151 (a k) (relation_zero k) (e k 30)
lemma extension_1404_56 : a k 56*normalRep k 1404=normalRep k 1457 := by
  change a k 56*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1176 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1404 (b : Fin 75) : a k b*normalRep k 1404 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1404_54 k]
      exact normal_mem k 1458
    · rw [extension_1404_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1404_56 k]
      exact normal_mem k 1457
  · rw [show a k b*normalRep k 1404=0 from arrow_incompatible k b 30 38 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1404) h]
    exact Submodule.zero_mem _
lemma extension_1405_5 : a k 5*normalRep k 1405=normalRep k 1459 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1405 (b : Fin 75) : a k b*normalRep k 1405 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1405_5 k]
      exact normal_mem k 1459
  · rw [show a k b*normalRep k 1405=0 from arrow_incompatible k b 31 5 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1405) h]
    exact Submodule.zero_mem _
lemma extension_1406_33 : a k 33*normalRep k 1406=0 := by
  change a k 33*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1142 (a k) (relation_zero k) (e k 31)
lemma extension_1406_34 : a k 34*normalRep k 1406=normalRep k 1459 := by
  change a k 34*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1179 (a k) (relation_zero k) (e k 31)
lemma arrow_span_1406 (b : Fin 75) : a k b*normalRep k 1406 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1406_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1406_34 k]
      exact normal_mem k 1459
  · rw [show a k b*normalRep k 1406=0 from arrow_incompatible k b 31 26 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1406) h]
    exact Submodule.zero_mem _
lemma extension_1407_63 : a k 63*normalRep k 1407=normalRep k 1460 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1407_64 : a k 64*normalRep k 1407=0 := by
  change a k 64*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1145 (a k) (relation_zero k) (e k 32)
lemma extension_1407_65 : a k 65*normalRep k 1407=0 := by
  change a k 65*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1155 (a k) (relation_zero k) (e k 32)
lemma arrow_span_1407 (b : Fin 75) : a k b*normalRep k 1407 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1407_63 k]
      exact normal_mem k 1460
    · rw [extension_1407_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1407_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1407=0 from arrow_incompatible k b 32 41 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1407) h]
    exact Submodule.zero_mem _
lemma extension_1408_63 : a k 63*normalRep k 1408=normalRep k 1461 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1408_64 : a k 64*normalRep k 1408=0 := by
  change a k 64*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1146 (a k) (relation_zero k) (e k 33)
lemma extension_1408_65 : a k 65*normalRep k 1408=0 := by
  change a k 65*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1156 (a k) (relation_zero k) (e k 33)
lemma arrow_span_1408 (b : Fin 75) : a k b*normalRep k 1408 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1408_63 k]
      exact normal_mem k 1461
    · rw [extension_1408_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1408_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1408=0 from arrow_incompatible k b 33 41 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1408) h]
    exact Submodule.zero_mem _
lemma extension_1409_20 : a k 20*normalRep k 1409=normalRep k 1462 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1409_21 : a k 21*normalRep k 1409=0 := by
  change a k 21*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1183 (a k) (relation_zero k) (e k 34)
lemma arrow_span_1409 (b : Fin 75) : a k b*normalRep k 1409 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1409_20 k]
      exact normal_mem k 1462
    · rw [extension_1409_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1409=0 from arrow_incompatible k b 34 18 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1409) h]
    exact Submodule.zero_mem _
lemma extension_1410_0 : a k 0*normalRep k 1410=normalRep k 1463 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1410 (b : Fin 75) : a k b*normalRep k 1410 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1410_0 k]
      exact normal_mem k 1463
  · rw [show a k b*normalRep k 1410=0 from arrow_incompatible k b 35 0 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1410) h]
    exact Submodule.zero_mem _
lemma extension_1411_30 : a k 30*normalRep k 1411=normalRep k 1464 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1411_31 : a k 31*normalRep k 1411=0 := by
  change a k 31*walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1166 (a k) (relation_zero k) (e k 36)
lemma arrow_span_1411 (b : Fin 75) : a k b*normalRep k 1411 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1411_30 k]
      exact normal_mem k 1464
    · rw [extension_1411_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1411=0 from arrow_incompatible k b 36 24 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1411) h]
    exact Submodule.zero_mem _
lemma extension_1412_57 : a k 57*normalRep k 1412=normalRep k 1465 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1412_58 : a k 58*normalRep k 1412=normalRep k 1466 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1412_59 : a k 59*normalRep k 1412=0 := by
  change a k 59*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1161 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1412 (b : Fin 75) : a k b*normalRep k 1412 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1412_57 k]
      exact normal_mem k 1465
    · rw [extension_1412_58 k]
      exact normal_mem k 1466
    · rw [extension_1412_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1412=0 from arrow_incompatible k b 37 39 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1412) h]
    exact Submodule.zero_mem _
lemma extension_1413_1 : a k 1*normalRep k 1413=normalRep k 1466 := by
  change a k 1*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1159 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1413 (b : Fin 75) : a k b*normalRep k 1413 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1413_1 k]
      exact normal_mem k 1466
  · rw [show a k b*normalRep k 1413=0 from arrow_incompatible k b 37 1 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1413) h]
    exact Submodule.zero_mem _
lemma extension_1414_5 : a k 5*normalRep k 1414=normalRep k 1467 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1414 (b : Fin 75) : a k b*normalRep k 1414 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1414_5 k]
      exact normal_mem k 1467
  · rw [show a k b*normalRep k 1414=0 from arrow_incompatible k b 38 5 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1414) h]
    exact Submodule.zero_mem _
lemma extension_1415_33 : a k 33*normalRep k 1415=0 := by
  change a k 33*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1143 (a k) (relation_zero k) (e k 38)
lemma extension_1415_34 : a k 34*normalRep k 1415=normalRep k 1467 := by
  change a k 34*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1180 (a k) (relation_zero k) (e k 38)
lemma arrow_span_1415 (b : Fin 75) : a k b*normalRep k 1415 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1415_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1415_34 k]
      exact normal_mem k 1467
  · rw [show a k b*normalRep k 1415=0 from arrow_incompatible k b 38 26 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1415) h]
    exact Submodule.zero_mem _
lemma extension_1416_20 : a k 20*normalRep k 1416=normalRep k 1468 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1416_21 : a k 21*normalRep k 1416=0 := by
  change a k 21*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1184 (a k) (relation_zero k) (e k 39)
lemma arrow_span_1416 (b : Fin 75) : a k b*normalRep k 1416 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1416_20 k]
      exact normal_mem k 1468
    · rw [extension_1416_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1416=0 from arrow_incompatible k b 39 18 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1416) h]
    exact Submodule.zero_mem _
lemma extension_1417_43 : a k 43*normalRep k 1417=0 := by
  change a k 43*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1153 (a k) (relation_zero k) (e k 40)
lemma extension_1417_44 : a k 44*normalRep k 1417=normalRep k 1469 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1417 (b : Fin 75) : a k b*normalRep k 1417 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1417_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1417_44 k]
      exact normal_mem k 1469
  · rw [show a k b*normalRep k 1417=0 from arrow_incompatible k b 40 32 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1417) h]
    exact Submodule.zero_mem _
lemma extension_1418_15 : a k 15*normalRep k 1418=normalRep k 1470 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1418_16 : a k 16*normalRep k 1418=normalRep k 1469 := by
  change a k 16*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1178 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1418 (b : Fin 75) : a k b*normalRep k 1418 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1418_15 k]
      exact normal_mem k 1470
    · rw [extension_1418_16 k]
      exact normal_mem k 1469
  · rw [show a k b*normalRep k 1418=0 from arrow_incompatible k b 40 15 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1418) h]
    exact Submodule.zero_mem _
lemma extension_1419_2 : a k 2*normalRep k 1419=normalRep k 1471 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1419 (b : Fin 75) : a k b*normalRep k 1419 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1419_2 k]
      exact normal_mem k 1471
  · rw [show a k b*normalRep k 1419=0 from arrow_incompatible k b 41 2 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1419) h]
    exact Submodule.zero_mem _
lemma extension_1420_9 : a k 9*normalRep k 1420=normalRep k 1472 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1420 (b : Fin 75) : a k b*normalRep k 1420 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1420_9 k]
      exact normal_mem k 1472
  · rw [show a k b*normalRep k 1420=0 from arrow_incompatible k b 42 9 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1420) h]
    exact Submodule.zero_mem _
lemma extension_1421_52 : a k 52*normalRep k 1421=normalRep k 1472 := by
  change a k 52*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1163 (a k) (relation_zero k) (e k 42)
lemma extension_1421_53 : a k 53*normalRep k 1421=normalRep k 1473 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1421 (b : Fin 75) : a k b*normalRep k 1421 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1421_52 k]
      exact normal_mem k 1472
    · rw [extension_1421_53 k]
      exact normal_mem k 1473
  · rw [show a k b*normalRep k 1421=0 from arrow_incompatible k b 42 37 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1421) h]
    exact Submodule.zero_mem _
lemma extension_1422_4 : a k 4*normalRep k 1422=normalRep k 1473 := by
  change a k 4*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1181 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1422 (b : Fin 75) : a k b*normalRep k 1422 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1422_4 k]
      exact normal_mem k 1473
  · rw [show a k b*normalRep k 1422=0 from arrow_incompatible k b 42 4 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1422) h]
    exact Submodule.zero_mem _
lemma arrow_span_1423 (b : Fin 75) : a k b*normalRep k 1423 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1423=0 from arrow_incompatible k b 43 46 [69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1423) h]
    exact Submodule.zero_mem _
lemma arrow_span_1424 (b : Fin 75) : a k b*normalRep k 1424 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1424=0 from arrow_incompatible k b 43 46 [70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2, 0] (normal_endpoints 1424) h]
    exact Submodule.zero_mem _
lemma extension_1425_18 : a k 18*normalRep k 1425=normalRep k 1474 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_1425_19 : a k 19*normalRep k 1425=normalRep k 1475 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_1425 (b : Fin 75) : a k b*normalRep k 1425 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1425_18 k]
      exact normal_mem k 1474
    · rw [extension_1425_19 k]
      exact normal_mem k 1475
  · rw [show a k b*normalRep k 1425=0 from arrow_incompatible k b 44 17 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 1425) h]
    exact Submodule.zero_mem _
lemma extension_1426_60 : a k 60*normalRep k 1426=normalRep k 1476 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_1426_61 : a k 61*normalRep k 1426=0 := by
  change a k 61*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1169 (a k) (relation_zero k) (e k 44)
lemma extension_1426_62 : a k 62*normalRep k 1426=normalRep k 1475 := by
  change a k 62*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1170 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1426 (b : Fin 75) : a k b*normalRep k 1426 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1426_60 k]
      exact normal_mem k 1476
    · rw [extension_1426_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1426_62 k]
      exact normal_mem k 1475
  · rw [show a k b*normalRep k 1426=0 from arrow_incompatible k b 44 40 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 1426) h]
    exact Submodule.zero_mem _
lemma extension_1427_14 : a k 14*normalRep k 1427=normalRep k 1474 := by
  change a k 14*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1171 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1427 (b : Fin 75) : a k b*normalRep k 1427 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1427_14 k]
      exact normal_mem k 1474
  · rw [show a k b*normalRep k 1427=0 from arrow_incompatible k b 44 14 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 1427) h]
    exact Submodule.zero_mem _
lemma extension_1428_49 : a k 49*normalRep k 1428=normalRep k 1477 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] 49).symm
lemma arrow_span_1428 (b : Fin 75) : a k b*normalRep k 1428 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1428_49 k]
      exact normal_mem k 1477
  · rw [show a k b*normalRep k 1428=0 from arrow_incompatible k b 45 35 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13] (normal_endpoints 1428) h]
    exact Submodule.zero_mem _
lemma extension_1429_20 : a k 20*normalRep k 1429=0 := by
  change a k 20*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1162 (a k) (relation_zero k) (e k 45)
lemma extension_1429_21 : a k 21*normalRep k 1429=normalRep k 1478 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] 21).symm
lemma arrow_span_1429 (b : Fin 75) : a k b*normalRep k 1429 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1429_20 k]
      exact Submodule.zero_mem _
    · rw [extension_1429_21 k]
      exact normal_mem k 1478
  · rw [show a k b*normalRep k 1429=0 from arrow_incompatible k b 45 18 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63] (normal_endpoints 1429) h]
    exact Submodule.zero_mem _
lemma extension_1430_36 : a k 36*normalRep k 1430=normalRep k 1478 + normalRep k 1477 := by
  change a k 36*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] + walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1185 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1430 (b : Fin 75) : a k b*normalRep k 1430 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1430_36 k]
      exact (normalSpan k).add_mem (normal_mem k 1478) (normal_mem k 1477)
  · rw [show a k b*normalRep k 1430=0 from arrow_incompatible k b 45 28 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 64] (normal_endpoints 1430) h]
    exact Submodule.zero_mem _
lemma extension_1431_30 : a k 30*normalRep k 1431=normalRep k 1479 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1431_31 : a k 31*normalRep k 1431=0 := by
  change a k 31*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1207 (a k) (relation_zero k) (e k 6)
lemma arrow_span_1431 (b : Fin 75) : a k b*normalRep k 1431 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1431_30 k]
      exact normal_mem k 1479
    · rw [extension_1431_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1431=0 from arrow_incompatible k b 6 24 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1431) h]
    exact Submodule.zero_mem _
lemma extension_1432_2 : a k 2*normalRep k 1432=normalRep k 1480 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1432 (b : Fin 75) : a k b*normalRep k 1432 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1432_2 k]
      exact normal_mem k 1480
  · rw [show a k b*normalRep k 1432=0 from arrow_incompatible k b 7 2 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1432) h]
    exact Submodule.zero_mem _
lemma extension_1433_8 : a k 8*normalRep k 1433=normalRep k 1481 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_1433 (b : Fin 75) : a k b*normalRep k 1433 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1433_8 k]
      exact normal_mem k 1481
  · rw [show a k b*normalRep k 1433=0 from arrow_incompatible k b 10 8 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] (normal_endpoints 1433) h]
    exact Submodule.zero_mem _
lemma extension_1434_72 : a k 72*normalRep k 1434=normalRep k 1482 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] 72).symm
lemma extension_1434_73 : a k 73*normalRep k 1434=normalRep k 1481 := by
  change a k 73*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1228 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1434 (b : Fin 75) : a k b*normalRep k 1434 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1434_72 k]
      exact normal_mem k 1482
    · rw [extension_1434_73 k]
      exact normal_mem k 1481
  · rw [show a k b*normalRep k 1434=0 from arrow_incompatible k b 10 44 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] (normal_endpoints 1434) h]
    exact Submodule.zero_mem _
lemma extension_1435_22 : a k 22*normalRep k 1435=normalRep k 1483 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] 22).symm
lemma extension_1435_23 : a k 23*normalRep k 1435=normalRep k 1481 := by
  change a k 23*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1229 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1435 (b : Fin 75) : a k b*normalRep k 1435 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1435_22 k]
      exact normal_mem k 1483
    · rw [extension_1435_23 k]
      exact normal_mem k 1481
  · rw [show a k b*normalRep k 1435=0 from arrow_incompatible k b 10 19 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] (normal_endpoints 1435) h]
    exact Submodule.zero_mem _
lemma extension_1436_66 : a k 66*normalRep k 1436=normalRep k 1484 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_1436_67 : a k 67*normalRep k 1436=0 := by
  change a k 67*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1201 (a k) (relation_zero k) (e k 11)
lemma extension_1436_68 : a k 68*normalRep k 1436=normalRep k 1485 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_1436 (b : Fin 75) : a k b*normalRep k 1436 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1436_66 k]
      exact normal_mem k 1484
    · rw [extension_1436_67 k]
      exact Submodule.zero_mem _
    · rw [extension_1436_68 k]
      exact normal_mem k 1485
  · rw [show a k b*normalRep k 1436=0 from arrow_incompatible k b 11 42 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] (normal_endpoints 1436) h]
    exact Submodule.zero_mem _
lemma extension_1437_37 : a k 37*normalRep k 1437=normalRep k 1484 := by
  change a k 37*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1230 (a k) (relation_zero k) (e k 11)
lemma extension_1437_38 : a k 38*normalRep k 1437=normalRep k 1486 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_1437 (b : Fin 75) : a k b*normalRep k 1437 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1437_37 k]
      exact normal_mem k 1484
    · rw [extension_1437_38 k]
      exact normal_mem k 1486
  · rw [show a k b*normalRep k 1437=0 from arrow_incompatible k b 11 29 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] (normal_endpoints 1437) h]
    exact Submodule.zero_mem _
lemma extension_1438_3 : a k 3*normalRep k 1438=(-normalRep k 1485) := by
  change a k 3*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22]=(-walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1211 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1438 (b : Fin 75) : a k b*normalRep k 1438 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1438_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1485)
  · rw [show a k b*normalRep k 1438=0 from arrow_incompatible k b 11 3 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22] (normal_endpoints 1438) h]
    exact Submodule.zero_mem _
lemma extension_1439_57 : a k 57*normalRep k 1439=normalRep k 1487 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1439_58 : a k 58*normalRep k 1439=normalRep k 1488 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1439_59 : a k 59*normalRep k 1439=0 := by
  change a k 59*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1204 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1439 (b : Fin 75) : a k b*normalRep k 1439 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1439_57 k]
      exact normal_mem k 1487
    · rw [extension_1439_58 k]
      exact normal_mem k 1488
    · rw [extension_1439_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1439=0 from arrow_incompatible k b 12 39 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1439) h]
    exact Submodule.zero_mem _
lemma extension_1440_1 : a k 1*normalRep k 1440=normalRep k 1488 := by
  change a k 1*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1202 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1440 (b : Fin 75) : a k b*normalRep k 1440 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1440_1 k]
      exact normal_mem k 1488
  · rw [show a k b*normalRep k 1440=0 from arrow_incompatible k b 12 1 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1440) h]
    exact Submodule.zero_mem _
lemma extension_1441_0 : a k 0*normalRep k 1441=normalRep k 1489 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1441 (b : Fin 75) : a k b*normalRep k 1441 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1441_0 k]
      exact normal_mem k 1489
  · rw [show a k b*normalRep k 1441=0 from arrow_incompatible k b 13 0 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1441) h]
    exact Submodule.zero_mem _
lemma extension_1442_0 : a k 0*normalRep k 1442=normalRep k 1490 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1442 (b : Fin 75) : a k b*normalRep k 1442 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1442_0 k]
      exact normal_mem k 1490
  · rw [show a k b*normalRep k 1442=0 from arrow_incompatible k b 16 0 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1442) h]
    exact Submodule.zero_mem _
lemma arrow_span_1443 (b : Fin 75) : a k b*normalRep k 1443 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1443=0 from arrow_incompatible k b 18 46 [21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1443) h]
    exact Submodule.zero_mem _
lemma extension_1444_24 : a k 24*normalRep k 1444=normalRep k 1491 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_1444_25 : a k 25*normalRep k 1444=normalRep k 1492 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_1444 (b : Fin 75) : a k b*normalRep k 1444 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1444_24 k]
      exact normal_mem k 1491
    · rw [extension_1444_25 k]
      exact normal_mem k 1492
  · rw [show a k b*normalRep k 1444=0 from arrow_incompatible k b 21 20 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 1444) h]
    exact Submodule.zero_mem _
lemma extension_1445_39 : a k 39*normalRep k 1445=0 := by
  change a k 39*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1194 (a k) (relation_zero k) (e k 21)
lemma extension_1445_40 : a k 40*normalRep k 1445=(-normalRep k 1492) := by
  change a k 40*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1227 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1445 (b : Fin 75) : a k b*normalRep k 1445 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1445_39 k]
      exact Submodule.zero_mem _
    · rw [extension_1445_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1492)
  · rw [show a k b*normalRep k 1445=0 from arrow_incompatible k b 21 30 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 1445) h]
    exact Submodule.zero_mem _
lemma extension_1446_28 : a k 28*normalRep k 1446=normalRep k 1493 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_1446_29 : a k 29*normalRep k 1446=normalRep k 1491 := by
  change a k 29*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1216 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1446 (b : Fin 75) : a k b*normalRep k 1446 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1446_28 k]
      exact normal_mem k 1493
    · rw [extension_1446_29 k]
      exact normal_mem k 1491
  · rw [show a k b*normalRep k 1446=0 from arrow_incompatible k b 21 23 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 1446) h]
    exact Submodule.zero_mem _
lemma extension_1447_20 : a k 20*normalRep k 1447=normalRep k 1494 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1447_21 : a k 21*normalRep k 1447=0 := by
  change a k 21*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1224 (a k) (relation_zero k) (e k 22)
lemma arrow_span_1447 (b : Fin 75) : a k b*normalRep k 1447 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1447_20 k]
      exact normal_mem k 1494
    · rw [extension_1447_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1447=0 from arrow_incompatible k b 22 18 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1447) h]
    exact Submodule.zero_mem _
lemma extension_1448_18 : a k 18*normalRep k 1448=normalRep k 1495 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_1448_19 : a k 19*normalRep k 1448=normalRep k 1496 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_1448 (b : Fin 75) : a k b*normalRep k 1448 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1448_18 k]
      exact normal_mem k 1495
    · rw [extension_1448_19 k]
      exact normal_mem k 1496
  · rw [show a k b*normalRep k 1448=0 from arrow_incompatible k b 24 17 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 1448) h]
    exact Submodule.zero_mem _
lemma extension_1449_60 : a k 60*normalRep k 1449=normalRep k 1497 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_1449_61 : a k 61*normalRep k 1449=0 := by
  change a k 61*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1212 (a k) (relation_zero k) (e k 24)
lemma extension_1449_62 : a k 62*normalRep k 1449=normalRep k 1496 := by
  change a k 62*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1213 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1449 (b : Fin 75) : a k b*normalRep k 1449 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1449_60 k]
      exact normal_mem k 1497
    · rw [extension_1449_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1449_62 k]
      exact normal_mem k 1496
  · rw [show a k b*normalRep k 1449=0 from arrow_incompatible k b 24 40 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 1449) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
