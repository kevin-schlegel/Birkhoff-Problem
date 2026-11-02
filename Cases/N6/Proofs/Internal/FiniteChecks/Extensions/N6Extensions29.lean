import N6NormalData
import N6Reduced19
import N6Reduced20
import N6Reduced21
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_1450_14 : a k 14*normalRep k 1450=normalRep k 1495 := by
  change a k 14*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1214 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1450 (b : Fin 75) : a k b*normalRep k 1450 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1450_14 k]
      exact normal_mem k 1495
  · rw [show a k b*normalRep k 1450=0 from arrow_incompatible k b 24 14 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 1450) h]
    exact Submodule.zero_mem _
lemma extension_1451_43 : a k 43*normalRep k 1451=0 := by
  change a k 43*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1197 (a k) (relation_zero k) (e k 25)
lemma extension_1451_44 : a k 44*normalRep k 1451=normalRep k 1498 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1451 (b : Fin 75) : a k b*normalRep k 1451 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1451_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1451_44 k]
      exact normal_mem k 1498
  · rw [show a k b*normalRep k 1451=0 from arrow_incompatible k b 25 32 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1451) h]
    exact Submodule.zero_mem _
lemma extension_1452_15 : a k 15*normalRep k 1452=normalRep k 1499 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1452_16 : a k 16*normalRep k 1452=normalRep k 1498 := by
  change a k 16*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1219 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1452 (b : Fin 75) : a k b*normalRep k 1452 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1452_15 k]
      exact normal_mem k 1499
    · rw [extension_1452_16 k]
      exact normal_mem k 1498
  · rw [show a k b*normalRep k 1452=0 from arrow_incompatible k b 25 15 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1452) h]
    exact Submodule.zero_mem _
lemma extension_1453_2 : a k 2*normalRep k 1453=normalRep k 1500 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1453 (b : Fin 75) : a k b*normalRep k 1453 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1453_2 k]
      exact normal_mem k 1500
  · rw [show a k b*normalRep k 1453=0 from arrow_incompatible k b 26 2 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1453) h]
    exact Submodule.zero_mem _
lemma extension_1454_5 : a k 5*normalRep k 1454=normalRep k 1501 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1454 (b : Fin 75) : a k b*normalRep k 1454 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1454_5 k]
      exact normal_mem k 1501
  · rw [show a k b*normalRep k 1454=0 from arrow_incompatible k b 27 5 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1454) h]
    exact Submodule.zero_mem _
lemma extension_1455_33 : a k 33*normalRep k 1455=0 := by
  change a k 33*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1190 (a k) (relation_zero k) (e k 27)
lemma extension_1455_34 : a k 34*normalRep k 1455=normalRep k 1501 := by
  change a k 34*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1221 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1455 (b : Fin 75) : a k b*normalRep k 1455 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1455_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1455_34 k]
      exact normal_mem k 1501
  · rw [show a k b*normalRep k 1455=0 from arrow_incompatible k b 27 26 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1455) h]
    exact Submodule.zero_mem _
lemma arrow_span_1456 (b : Fin 75) : a k b*normalRep k 1456 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1456=0 from arrow_incompatible k b 28 46 [36, 70, 22, 3, 40, 60, 4, 54, 15, 1, 34, 63, 20, 30, 2, 0] (normal_endpoints 1456) h]
    exact Submodule.zero_mem _
lemma extension_1457_43 : a k 43*normalRep k 1457=0 := by
  change a k 43*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1198 (a k) (relation_zero k) (e k 30)
lemma extension_1457_44 : a k 44*normalRep k 1457=normalRep k 1502 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1457 (b : Fin 75) : a k b*normalRep k 1457 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1457_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1457_44 k]
      exact normal_mem k 1502
  · rw [show a k b*normalRep k 1457=0 from arrow_incompatible k b 30 32 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1457) h]
    exact Submodule.zero_mem _
lemma extension_1458_15 : a k 15*normalRep k 1458=normalRep k 1503 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1458_16 : a k 16*normalRep k 1458=normalRep k 1502 := by
  change a k 16*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1220 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1458 (b : Fin 75) : a k b*normalRep k 1458 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1458_15 k]
      exact normal_mem k 1503
    · rw [extension_1458_16 k]
      exact normal_mem k 1502
  · rw [show a k b*normalRep k 1458=0 from arrow_incompatible k b 30 15 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1458) h]
    exact Submodule.zero_mem _
lemma extension_1459_63 : a k 63*normalRep k 1459=normalRep k 1504 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1459_64 : a k 64*normalRep k 1459=0 := by
  change a k 64*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1192 (a k) (relation_zero k) (e k 31)
lemma extension_1459_65 : a k 65*normalRep k 1459=0 := by
  change a k 65*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1199 (a k) (relation_zero k) (e k 31)
lemma arrow_span_1459 (b : Fin 75) : a k b*normalRep k 1459 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1459_63 k]
      exact normal_mem k 1504
    · rw [extension_1459_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1459_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1459=0 from arrow_incompatible k b 31 41 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1459) h]
    exact Submodule.zero_mem _
lemma extension_1460_20 : a k 20*normalRep k 1460=normalRep k 1505 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1460_21 : a k 21*normalRep k 1460=0 := by
  change a k 21*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1225 (a k) (relation_zero k) (e k 32)
lemma arrow_span_1460 (b : Fin 75) : a k b*normalRep k 1460 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1460_20 k]
      exact normal_mem k 1505
    · rw [extension_1460_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1460=0 from arrow_incompatible k b 32 18 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1460) h]
    exact Submodule.zero_mem _
lemma extension_1461_20 : a k 20*normalRep k 1461=normalRep k 1506 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1461_21 : a k 21*normalRep k 1461=0 := by
  change a k 21*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1226 (a k) (relation_zero k) (e k 33)
lemma arrow_span_1461 (b : Fin 75) : a k b*normalRep k 1461 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1461_20 k]
      exact normal_mem k 1506
    · rw [extension_1461_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1461=0 from arrow_incompatible k b 33 18 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1461) h]
    exact Submodule.zero_mem _
lemma extension_1462_30 : a k 30*normalRep k 1462=normalRep k 1507 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1462_31 : a k 31*normalRep k 1462=0 := by
  change a k 31*walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1208 (a k) (relation_zero k) (e k 34)
lemma arrow_span_1462 (b : Fin 75) : a k b*normalRep k 1462 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1462_30 k]
      exact normal_mem k 1507
    · rw [extension_1462_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1462=0 from arrow_incompatible k b 34 24 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1462) h]
    exact Submodule.zero_mem _
lemma arrow_span_1463 (b : Fin 75) : a k b*normalRep k 1463 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1463=0 from arrow_incompatible k b 35 46 [49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1463) h]
    exact Submodule.zero_mem _
lemma extension_1464_2 : a k 2*normalRep k 1464=normalRep k 1508 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1464 (b : Fin 75) : a k b*normalRep k 1464 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1464_2 k]
      exact normal_mem k 1508
  · rw [show a k b*normalRep k 1464=0 from arrow_incompatible k b 36 2 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1464) h]
    exact Submodule.zero_mem _
lemma extension_1465_5 : a k 5*normalRep k 1465=normalRep k 1509 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1465 (b : Fin 75) : a k b*normalRep k 1465 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1465_5 k]
      exact normal_mem k 1509
  · rw [show a k b*normalRep k 1465=0 from arrow_incompatible k b 37 5 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1465) h]
    exact Submodule.zero_mem _
lemma extension_1466_33 : a k 33*normalRep k 1466=0 := by
  change a k 33*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1191 (a k) (relation_zero k) (e k 37)
lemma extension_1466_34 : a k 34*normalRep k 1466=normalRep k 1509 := by
  change a k 34*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1222 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1466 (b : Fin 75) : a k b*normalRep k 1466 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1466_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1466_34 k]
      exact normal_mem k 1509
  · rw [show a k b*normalRep k 1466=0 from arrow_incompatible k b 37 26 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1466) h]
    exact Submodule.zero_mem _
lemma extension_1467_63 : a k 63*normalRep k 1467=normalRep k 1510 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1467_64 : a k 64*normalRep k 1467=0 := by
  change a k 64*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1193 (a k) (relation_zero k) (e k 38)
lemma extension_1467_65 : a k 65*normalRep k 1467=0 := by
  change a k 65*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1200 (a k) (relation_zero k) (e k 38)
lemma arrow_span_1467 (b : Fin 75) : a k b*normalRep k 1467 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1467_63 k]
      exact normal_mem k 1510
    · rw [extension_1467_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1467_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1467=0 from arrow_incompatible k b 38 41 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1467) h]
    exact Submodule.zero_mem _
lemma extension_1468_30 : a k 30*normalRep k 1468=normalRep k 1511 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1468_31 : a k 31*normalRep k 1468=0 := by
  change a k 31*walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1209 (a k) (relation_zero k) (e k 39)
lemma arrow_span_1468 (b : Fin 75) : a k b*normalRep k 1468 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1468_30 k]
      exact normal_mem k 1511
    · rw [extension_1468_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1468=0 from arrow_incompatible k b 39 24 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1468) h]
    exact Submodule.zero_mem _
lemma extension_1469_57 : a k 57*normalRep k 1469=normalRep k 1512 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1469_58 : a k 58*normalRep k 1469=normalRep k 1513 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1469_59 : a k 59*normalRep k 1469=0 := by
  change a k 59*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1205 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1469 (b : Fin 75) : a k b*normalRep k 1469 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1469_57 k]
      exact normal_mem k 1512
    · rw [extension_1469_58 k]
      exact normal_mem k 1513
    · rw [extension_1469_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1469=0 from arrow_incompatible k b 40 39 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1469) h]
    exact Submodule.zero_mem _
lemma extension_1470_1 : a k 1*normalRep k 1470=normalRep k 1513 := by
  change a k 1*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1203 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1470 (b : Fin 75) : a k b*normalRep k 1470 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1470_1 k]
      exact normal_mem k 1513
  · rw [show a k b*normalRep k 1470=0 from arrow_incompatible k b 40 1 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1470) h]
    exact Submodule.zero_mem _
lemma extension_1471_0 : a k 0*normalRep k 1471=normalRep k 1514 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1471 (b : Fin 75) : a k b*normalRep k 1471 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1471_0 k]
      exact normal_mem k 1514
  · rw [show a k b*normalRep k 1471=0 from arrow_incompatible k b 41 0 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1471) h]
    exact Submodule.zero_mem _
lemma extension_1472_41 : a k 41*normalRep k 1472=normalRep k 1515 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1472_42 : a k 42*normalRep k 1472=0 := by
  change a k 42*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1195 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1472 (b : Fin 75) : a k b*normalRep k 1472 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1472_41 k]
      exact normal_mem k 1515
    · rw [extension_1472_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1472=0 from arrow_incompatible k b 42 31 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1472) h]
    exact Submodule.zero_mem _
lemma extension_1473_54 : a k 54*normalRep k 1473=normalRep k 1516 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1473_55 : a k 55*normalRep k 1473=0 := by
  change a k 55*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1196 (a k) (relation_zero k) (e k 42)
lemma extension_1473_56 : a k 56*normalRep k 1473=normalRep k 1515 := by
  change a k 56*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1218 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1473 (b : Fin 75) : a k b*normalRep k 1473 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1473_54 k]
      exact normal_mem k 1516
    · rw [extension_1473_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1473_56 k]
      exact normal_mem k 1515
  · rw [show a k b*normalRep k 1473=0 from arrow_incompatible k b 42 38 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1473) h]
    exact Submodule.zero_mem _
lemma extension_1474_9 : a k 9*normalRep k 1474=normalRep k 1517 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1474 (b : Fin 75) : a k b*normalRep k 1474 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1474_9 k]
      exact normal_mem k 1517
  · rw [show a k b*normalRep k 1474=0 from arrow_incompatible k b 44 9 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1474) h]
    exact Submodule.zero_mem _
lemma extension_1475_52 : a k 52*normalRep k 1475=normalRep k 1517 := by
  change a k 52*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1206 (a k) (relation_zero k) (e k 44)
lemma extension_1475_53 : a k 53*normalRep k 1475=normalRep k 1518 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1475 (b : Fin 75) : a k b*normalRep k 1475 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1475_52 k]
      exact normal_mem k 1517
    · rw [extension_1475_53 k]
      exact normal_mem k 1518
  · rw [show a k b*normalRep k 1475=0 from arrow_incompatible k b 44 37 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1475) h]
    exact Submodule.zero_mem _
lemma extension_1476_4 : a k 4*normalRep k 1476=normalRep k 1518 := by
  change a k 4*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1223 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1476 (b : Fin 75) : a k b*normalRep k 1476 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1476_4 k]
      exact normal_mem k 1518
  · rw [show a k b*normalRep k 1476=0 from arrow_incompatible k b 44 4 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1476) h]
    exact Submodule.zero_mem _
lemma extension_1477_69 : a k 69*normalRep k 1477=normalRep k 1519 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 69).symm
lemma extension_1477_70 : a k 70*normalRep k 1477=0 := by
  change a k 70*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1217 (a k) (relation_zero k) (e k 45)
lemma extension_1477_71 : a k 71*normalRep k 1477=normalRep k 1520 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] 71).symm
lemma arrow_span_1477 (b : Fin 75) : a k b*normalRep k 1477 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1477_69 k]
      exact normal_mem k 1519
    · rw [extension_1477_70 k]
      exact Submodule.zero_mem _
    · rw [extension_1477_71 k]
      exact normal_mem k 1520
  · rw [show a k b*normalRep k 1477=0 from arrow_incompatible k b 45 43 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49] (normal_endpoints 1477) h]
    exact Submodule.zero_mem _
lemma extension_1478_69 : a k 69*normalRep k 1478=(-normalRep k 1519) := by
  change a k 69*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=(-walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1215 (a k) (relation_zero k) (e k 45)
lemma extension_1478_70 : a k 70*normalRep k 1478=normalRep k 1521 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] 70).symm
lemma extension_1478_71 : a k 71*normalRep k 1478=0 := by
  change a k 71*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1210 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1478 (b : Fin 75) : a k b*normalRep k 1478 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1478_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1519)
    · rw [extension_1478_70 k]
      exact normal_mem k 1521
    · rw [extension_1478_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1478=0 from arrow_incompatible k b 45 43 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21] (normal_endpoints 1478) h]
    exact Submodule.zero_mem _
lemma extension_1479_2 : a k 2*normalRep k 1479=normalRep k 1522 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1479 (b : Fin 75) : a k b*normalRep k 1479 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1479_2 k]
      exact normal_mem k 1522
  · rw [show a k b*normalRep k 1479=0 from arrow_incompatible k b 6 2 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1479) h]
    exact Submodule.zero_mem _
lemma extension_1480_0 : a k 0*normalRep k 1480=normalRep k 1523 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1480 (b : Fin 75) : a k b*normalRep k 1480 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1480_0 k]
      exact normal_mem k 1523
  · rw [show a k b*normalRep k 1480=0 from arrow_incompatible k b 7 0 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1480) h]
    exact Submodule.zero_mem _
lemma extension_1481_66 : a k 66*normalRep k 1481=normalRep k 1524 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_1481_67 : a k 67*normalRep k 1481=0 := by
  change a k 67*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1241 (a k) (relation_zero k) (e k 10)
lemma extension_1481_68 : a k 68*normalRep k 1481=normalRep k 1525 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_1481 (b : Fin 75) : a k b*normalRep k 1481 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1481_66 k]
      exact normal_mem k 1524
    · rw [extension_1481_67 k]
      exact Submodule.zero_mem _
    · rw [extension_1481_68 k]
      exact normal_mem k 1525
  · rw [show a k b*normalRep k 1481=0 from arrow_incompatible k b 10 42 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] (normal_endpoints 1481) h]
    exact Submodule.zero_mem _
lemma extension_1482_37 : a k 37*normalRep k 1482=normalRep k 1524 := by
  change a k 37*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1265 (a k) (relation_zero k) (e k 10)
lemma extension_1482_38 : a k 38*normalRep k 1482=normalRep k 1526 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_1482 (b : Fin 75) : a k b*normalRep k 1482 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1482_37 k]
      exact normal_mem k 1524
    · rw [extension_1482_38 k]
      exact normal_mem k 1526
  · rw [show a k b*normalRep k 1482=0 from arrow_incompatible k b 10 29 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] (normal_endpoints 1482) h]
    exact Submodule.zero_mem _
lemma extension_1483_3 : a k 3*normalRep k 1483=(-normalRep k 1525) := by
  change a k 3*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22]=(-walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1250 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1483 (b : Fin 75) : a k b*normalRep k 1483 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1483_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1525)
  · rw [show a k b*normalRep k 1483=0 from arrow_incompatible k b 10 3 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22] (normal_endpoints 1483) h]
    exact Submodule.zero_mem _
lemma extension_1484_24 : a k 24*normalRep k 1484=normalRep k 1527 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_1484_25 : a k 25*normalRep k 1484=normalRep k 1528 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_1484 (b : Fin 75) : a k b*normalRep k 1484 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1484_24 k]
      exact normal_mem k 1527
    · rw [extension_1484_25 k]
      exact normal_mem k 1528
  · rw [show a k b*normalRep k 1484=0 from arrow_incompatible k b 11 20 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 1484) h]
    exact Submodule.zero_mem _
lemma extension_1485_39 : a k 39*normalRep k 1485=0 := by
  change a k 39*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1235 (a k) (relation_zero k) (e k 11)
lemma extension_1485_40 : a k 40*normalRep k 1485=(-normalRep k 1528) := by
  change a k 40*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1262 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1485 (b : Fin 75) : a k b*normalRep k 1485 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1485_39 k]
      exact Submodule.zero_mem _
    · rw [extension_1485_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1528)
  · rw [show a k b*normalRep k 1485=0 from arrow_incompatible k b 11 30 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 1485) h]
    exact Submodule.zero_mem _
lemma extension_1486_28 : a k 28*normalRep k 1486=normalRep k 1529 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_1486_29 : a k 29*normalRep k 1486=normalRep k 1527 := by
  change a k 29*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1254 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1486 (b : Fin 75) : a k b*normalRep k 1486 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1486_28 k]
      exact normal_mem k 1529
    · rw [extension_1486_29 k]
      exact normal_mem k 1527
  · rw [show a k b*normalRep k 1486=0 from arrow_incompatible k b 11 23 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 1486) h]
    exact Submodule.zero_mem _
lemma extension_1487_5 : a k 5*normalRep k 1487=normalRep k 1530 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1487 (b : Fin 75) : a k b*normalRep k 1487 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1487_5 k]
      exact normal_mem k 1530
  · rw [show a k b*normalRep k 1487=0 from arrow_incompatible k b 12 5 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1487) h]
    exact Submodule.zero_mem _
lemma extension_1488_33 : a k 33*normalRep k 1488=0 := by
  change a k 33*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1231 (a k) (relation_zero k) (e k 12)
lemma extension_1488_34 : a k 34*normalRep k 1488=normalRep k 1530 := by
  change a k 34*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1257 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1488 (b : Fin 75) : a k b*normalRep k 1488 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1488_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1488_34 k]
      exact normal_mem k 1530
  · rw [show a k b*normalRep k 1488=0 from arrow_incompatible k b 12 26 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1488) h]
    exact Submodule.zero_mem _
lemma arrow_span_1489 (b : Fin 75) : a k b*normalRep k 1489 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1489=0 from arrow_incompatible k b 13 46 [13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1489) h]
    exact Submodule.zero_mem _
lemma arrow_span_1490 (b : Fin 75) : a k b*normalRep k 1490 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1490=0 from arrow_incompatible k b 16 46 [17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1490) h]
    exact Submodule.zero_mem _
lemma extension_1491_18 : a k 18*normalRep k 1491=normalRep k 1531 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_1491_19 : a k 19*normalRep k 1491=normalRep k 1532 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_1491 (b : Fin 75) : a k b*normalRep k 1491 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1491_18 k]
      exact normal_mem k 1531
    · rw [extension_1491_19 k]
      exact normal_mem k 1532
  · rw [show a k b*normalRep k 1491=0 from arrow_incompatible k b 21 17 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 1491) h]
    exact Submodule.zero_mem _
lemma extension_1492_60 : a k 60*normalRep k 1492=normalRep k 1533 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_1492_61 : a k 61*normalRep k 1492=0 := by
  change a k 61*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1251 (a k) (relation_zero k) (e k 21)
lemma extension_1492_62 : a k 62*normalRep k 1492=normalRep k 1532 := by
  change a k 62*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1252 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1492 (b : Fin 75) : a k b*normalRep k 1492 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1492_60 k]
      exact normal_mem k 1533
    · rw [extension_1492_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1492_62 k]
      exact normal_mem k 1532
  · rw [show a k b*normalRep k 1492=0 from arrow_incompatible k b 21 40 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 1492) h]
    exact Submodule.zero_mem _
lemma extension_1493_14 : a k 14*normalRep k 1493=normalRep k 1531 := by
  change a k 14*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1253 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1493 (b : Fin 75) : a k b*normalRep k 1493 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1493_14 k]
      exact normal_mem k 1531
  · rw [show a k b*normalRep k 1493=0 from arrow_incompatible k b 21 14 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 1493) h]
    exact Submodule.zero_mem _
lemma extension_1494_30 : a k 30*normalRep k 1494=normalRep k 1534 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1494_31 : a k 31*normalRep k 1494=0 := by
  change a k 31*walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1247 (a k) (relation_zero k) (e k 22)
lemma arrow_span_1494 (b : Fin 75) : a k b*normalRep k 1494 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1494_30 k]
      exact normal_mem k 1534
    · rw [extension_1494_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1494=0 from arrow_incompatible k b 22 24 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1494) h]
    exact Submodule.zero_mem _
lemma extension_1495_9 : a k 9*normalRep k 1495=normalRep k 1535 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1495 (b : Fin 75) : a k b*normalRep k 1495 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1495_9 k]
      exact normal_mem k 1535
  · rw [show a k b*normalRep k 1495=0 from arrow_incompatible k b 24 9 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1495) h]
    exact Submodule.zero_mem _
lemma extension_1496_52 : a k 52*normalRep k 1496=normalRep k 1535 := by
  change a k 52*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1246 (a k) (relation_zero k) (e k 24)
lemma extension_1496_53 : a k 53*normalRep k 1496=normalRep k 1536 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1496 (b : Fin 75) : a k b*normalRep k 1496 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1496_52 k]
      exact normal_mem k 1535
    · rw [extension_1496_53 k]
      exact normal_mem k 1536
  · rw [show a k b*normalRep k 1496=0 from arrow_incompatible k b 24 37 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1496) h]
    exact Submodule.zero_mem _
lemma extension_1497_4 : a k 4*normalRep k 1497=normalRep k 1536 := by
  change a k 4*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1259 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1497 (b : Fin 75) : a k b*normalRep k 1497 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1497_4 k]
      exact normal_mem k 1536
  · rw [show a k b*normalRep k 1497=0 from arrow_incompatible k b 24 4 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1497) h]
    exact Submodule.zero_mem _
lemma extension_1498_57 : a k 57*normalRep k 1498=normalRep k 1537 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1498_58 : a k 58*normalRep k 1498=normalRep k 1538 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1498_59 : a k 59*normalRep k 1498=0 := by
  change a k 59*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1244 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1498 (b : Fin 75) : a k b*normalRep k 1498 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1498_57 k]
      exact normal_mem k 1537
    · rw [extension_1498_58 k]
      exact normal_mem k 1538
    · rw [extension_1498_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1498=0 from arrow_incompatible k b 25 39 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1498) h]
    exact Submodule.zero_mem _
lemma extension_1499_1 : a k 1*normalRep k 1499=normalRep k 1538 := by
  change a k 1*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1242 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1499 (b : Fin 75) : a k b*normalRep k 1499 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1499_1 k]
      exact normal_mem k 1538
  · rw [show a k b*normalRep k 1499=0 from arrow_incompatible k b 25 1 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1499) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
