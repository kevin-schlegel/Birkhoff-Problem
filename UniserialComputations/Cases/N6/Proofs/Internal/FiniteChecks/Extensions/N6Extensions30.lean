import N6NormalData
import N6Reduced20
import N6Reduced21
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_1500_0 : a k 0*normalRep k 1500=normalRep k 1539 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1500 (b : Fin 75) : a k b*normalRep k 1500 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1500_0 k]
      exact normal_mem k 1539
  · rw [show a k b*normalRep k 1500=0 from arrow_incompatible k b 26 0 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1500) h]
    exact Submodule.zero_mem _
lemma extension_1501_63 : a k 63*normalRep k 1501=normalRep k 1540 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1501_64 : a k 64*normalRep k 1501=0 := by
  change a k 64*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1233 (a k) (relation_zero k) (e k 27)
lemma extension_1501_65 : a k 65*normalRep k 1501=0 := by
  change a k 65*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1239 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1501 (b : Fin 75) : a k b*normalRep k 1501 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1501_63 k]
      exact normal_mem k 1540
    · rw [extension_1501_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1501_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1501=0 from arrow_incompatible k b 27 41 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1501) h]
    exact Submodule.zero_mem _
lemma extension_1502_57 : a k 57*normalRep k 1502=normalRep k 1541 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1502_58 : a k 58*normalRep k 1502=normalRep k 1542 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1502_59 : a k 59*normalRep k 1502=0 := by
  change a k 59*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1245 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1502 (b : Fin 75) : a k b*normalRep k 1502 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1502_57 k]
      exact normal_mem k 1541
    · rw [extension_1502_58 k]
      exact normal_mem k 1542
    · rw [extension_1502_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1502=0 from arrow_incompatible k b 30 39 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1502) h]
    exact Submodule.zero_mem _
lemma extension_1503_1 : a k 1*normalRep k 1503=normalRep k 1542 := by
  change a k 1*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1243 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1503 (b : Fin 75) : a k b*normalRep k 1503 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1503_1 k]
      exact normal_mem k 1542
  · rw [show a k b*normalRep k 1503=0 from arrow_incompatible k b 30 1 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1503) h]
    exact Submodule.zero_mem _
lemma extension_1504_20 : a k 20*normalRep k 1504=normalRep k 1543 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1504_21 : a k 21*normalRep k 1504=0 := by
  change a k 21*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1260 (a k) (relation_zero k) (e k 31)
lemma arrow_span_1504 (b : Fin 75) : a k b*normalRep k 1504 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1504_20 k]
      exact normal_mem k 1543
    · rw [extension_1504_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1504=0 from arrow_incompatible k b 31 18 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1504) h]
    exact Submodule.zero_mem _
lemma extension_1505_30 : a k 30*normalRep k 1505=normalRep k 1544 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1505_31 : a k 31*normalRep k 1505=0 := by
  change a k 31*walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1248 (a k) (relation_zero k) (e k 32)
lemma arrow_span_1505 (b : Fin 75) : a k b*normalRep k 1505 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1505_30 k]
      exact normal_mem k 1544
    · rw [extension_1505_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1505=0 from arrow_incompatible k b 32 24 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1505) h]
    exact Submodule.zero_mem _
lemma extension_1506_30 : a k 30*normalRep k 1506=normalRep k 1545 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1506_31 : a k 31*normalRep k 1506=0 := by
  change a k 31*walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1249 (a k) (relation_zero k) (e k 33)
lemma arrow_span_1506 (b : Fin 75) : a k b*normalRep k 1506 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1506_30 k]
      exact normal_mem k 1545
    · rw [extension_1506_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1506=0 from arrow_incompatible k b 33 24 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1506) h]
    exact Submodule.zero_mem _
lemma extension_1507_2 : a k 2*normalRep k 1507=normalRep k 1546 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1507 (b : Fin 75) : a k b*normalRep k 1507 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1507_2 k]
      exact normal_mem k 1546
  · rw [show a k b*normalRep k 1507=0 from arrow_incompatible k b 34 2 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1507) h]
    exact Submodule.zero_mem _
lemma extension_1508_0 : a k 0*normalRep k 1508=normalRep k 1547 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1508 (b : Fin 75) : a k b*normalRep k 1508 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1508_0 k]
      exact normal_mem k 1547
  · rw [show a k b*normalRep k 1508=0 from arrow_incompatible k b 36 0 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1508) h]
    exact Submodule.zero_mem _
lemma extension_1509_63 : a k 63*normalRep k 1509=normalRep k 1548 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1509_64 : a k 64*normalRep k 1509=0 := by
  change a k 64*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1234 (a k) (relation_zero k) (e k 37)
lemma extension_1509_65 : a k 65*normalRep k 1509=0 := by
  change a k 65*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1240 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1509 (b : Fin 75) : a k b*normalRep k 1509 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1509_63 k]
      exact normal_mem k 1548
    · rw [extension_1509_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1509_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1509=0 from arrow_incompatible k b 37 41 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1509) h]
    exact Submodule.zero_mem _
lemma extension_1510_20 : a k 20*normalRep k 1510=normalRep k 1549 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1510_21 : a k 21*normalRep k 1510=0 := by
  change a k 21*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1261 (a k) (relation_zero k) (e k 38)
lemma arrow_span_1510 (b : Fin 75) : a k b*normalRep k 1510 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1510_20 k]
      exact normal_mem k 1549
    · rw [extension_1510_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1510=0 from arrow_incompatible k b 38 18 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1510) h]
    exact Submodule.zero_mem _
lemma extension_1511_2 : a k 2*normalRep k 1511=normalRep k 1550 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1511 (b : Fin 75) : a k b*normalRep k 1511 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1511_2 k]
      exact normal_mem k 1550
  · rw [show a k b*normalRep k 1511=0 from arrow_incompatible k b 39 2 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1511) h]
    exact Submodule.zero_mem _
lemma extension_1512_5 : a k 5*normalRep k 1512=normalRep k 1551 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1512 (b : Fin 75) : a k b*normalRep k 1512 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1512_5 k]
      exact normal_mem k 1551
  · rw [show a k b*normalRep k 1512=0 from arrow_incompatible k b 40 5 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1512) h]
    exact Submodule.zero_mem _
lemma extension_1513_33 : a k 33*normalRep k 1513=0 := by
  change a k 33*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1232 (a k) (relation_zero k) (e k 40)
lemma extension_1513_34 : a k 34*normalRep k 1513=normalRep k 1551 := by
  change a k 34*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1258 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1513 (b : Fin 75) : a k b*normalRep k 1513 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1513_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1513_34 k]
      exact normal_mem k 1551
  · rw [show a k b*normalRep k 1513=0 from arrow_incompatible k b 40 26 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1513) h]
    exact Submodule.zero_mem _
lemma arrow_span_1514 (b : Fin 75) : a k b*normalRep k 1514 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1514=0 from arrow_incompatible k b 41 46 [63, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1514) h]
    exact Submodule.zero_mem _
lemma extension_1515_43 : a k 43*normalRep k 1515=0 := by
  change a k 43*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1238 (a k) (relation_zero k) (e k 42)
lemma extension_1515_44 : a k 44*normalRep k 1515=normalRep k 1552 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1515 (b : Fin 75) : a k b*normalRep k 1515 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1515_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1515_44 k]
      exact normal_mem k 1552
  · rw [show a k b*normalRep k 1515=0 from arrow_incompatible k b 42 32 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1515) h]
    exact Submodule.zero_mem _
lemma extension_1516_15 : a k 15*normalRep k 1516=normalRep k 1553 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1516_16 : a k 16*normalRep k 1516=normalRep k 1552 := by
  change a k 16*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1256 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1516 (b : Fin 75) : a k b*normalRep k 1516 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1516_15 k]
      exact normal_mem k 1553
    · rw [extension_1516_16 k]
      exact normal_mem k 1552
  · rw [show a k b*normalRep k 1516=0 from arrow_incompatible k b 42 15 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1516) h]
    exact Submodule.zero_mem _
lemma extension_1517_41 : a k 41*normalRep k 1517=normalRep k 1554 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1517_42 : a k 42*normalRep k 1517=0 := by
  change a k 42*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1236 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1517 (b : Fin 75) : a k b*normalRep k 1517 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1517_41 k]
      exact normal_mem k 1554
    · rw [extension_1517_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1517=0 from arrow_incompatible k b 44 31 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1517) h]
    exact Submodule.zero_mem _
lemma extension_1518_54 : a k 54*normalRep k 1518=normalRep k 1555 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1518_55 : a k 55*normalRep k 1518=0 := by
  change a k 55*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1237 (a k) (relation_zero k) (e k 44)
lemma extension_1518_56 : a k 56*normalRep k 1518=normalRep k 1554 := by
  change a k 56*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1255 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1518 (b : Fin 75) : a k b*normalRep k 1518 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1518_54 k]
      exact normal_mem k 1555
    · rw [extension_1518_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1518_56 k]
      exact normal_mem k 1554
  · rw [show a k b*normalRep k 1518=0 from arrow_incompatible k b 44 38 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1518) h]
    exact Submodule.zero_mem _
lemma extension_1519_8 : a k 8*normalRep k 1519=normalRep k 1556 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_1519 (b : Fin 75) : a k b*normalRep k 1519 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1519_8 k]
      exact normal_mem k 1556
  · rw [show a k b*normalRep k 1519=0 from arrow_incompatible k b 45 8 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69] (normal_endpoints 1519) h]
    exact Submodule.zero_mem _
lemma extension_1520_72 : a k 72*normalRep k 1520=normalRep k 1557 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] 72).symm
lemma extension_1520_73 : a k 73*normalRep k 1520=normalRep k 1556 := by
  change a k 73*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1263 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1520 (b : Fin 75) : a k b*normalRep k 1520 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1520_72 k]
      exact normal_mem k 1557
    · rw [extension_1520_73 k]
      exact normal_mem k 1556
  · rw [show a k b*normalRep k 1520=0 from arrow_incompatible k b 45 44 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71] (normal_endpoints 1520) h]
    exact Submodule.zero_mem _
lemma extension_1521_22 : a k 22*normalRep k 1521=normalRep k 1558 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] 22).symm
lemma extension_1521_23 : a k 23*normalRep k 1521=normalRep k 1556 := by
  change a k 23*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1264 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1521 (b : Fin 75) : a k b*normalRep k 1521 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1521_22 k]
      exact normal_mem k 1558
    · rw [extension_1521_23 k]
      exact normal_mem k 1556
  · rw [show a k b*normalRep k 1521=0 from arrow_incompatible k b 45 19 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70] (normal_endpoints 1521) h]
    exact Submodule.zero_mem _
lemma extension_1522_0 : a k 0*normalRep k 1522=normalRep k 1559 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1522 (b : Fin 75) : a k b*normalRep k 1522 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1522_0 k]
      exact normal_mem k 1559
  · rw [show a k b*normalRep k 1522=0 from arrow_incompatible k b 6 0 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1522) h]
    exact Submodule.zero_mem _
lemma arrow_span_1523 (b : Fin 75) : a k b*normalRep k 1523 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1523=0 from arrow_incompatible k b 7 46 [7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1523) h]
    exact Submodule.zero_mem _
lemma extension_1524_24 : a k 24*normalRep k 1524=normalRep k 1560 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_1524_25 : a k 25*normalRep k 1524=normalRep k 1561 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_1524 (b : Fin 75) : a k b*normalRep k 1524 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1524_24 k]
      exact normal_mem k 1560
    · rw [extension_1524_25 k]
      exact normal_mem k 1561
  · rw [show a k b*normalRep k 1524=0 from arrow_incompatible k b 10 20 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 1524) h]
    exact Submodule.zero_mem _
lemma extension_1525_39 : a k 39*normalRep k 1525=0 := by
  change a k 39*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1270 (a k) (relation_zero k) (e k 10)
lemma extension_1525_40 : a k 40*normalRep k 1525=(-normalRep k 1561) := by
  change a k 40*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1294 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1525 (b : Fin 75) : a k b*normalRep k 1525 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1525_39 k]
      exact Submodule.zero_mem _
    · rw [extension_1525_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1561)
  · rw [show a k b*normalRep k 1525=0 from arrow_incompatible k b 10 30 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 1525) h]
    exact Submodule.zero_mem _
lemma extension_1526_28 : a k 28*normalRep k 1526=normalRep k 1562 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_1526_29 : a k 29*normalRep k 1526=normalRep k 1560 := by
  change a k 29*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1286 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1526 (b : Fin 75) : a k b*normalRep k 1526 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1526_28 k]
      exact normal_mem k 1562
    · rw [extension_1526_29 k]
      exact normal_mem k 1560
  · rw [show a k b*normalRep k 1526=0 from arrow_incompatible k b 10 23 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 1526) h]
    exact Submodule.zero_mem _
lemma extension_1527_18 : a k 18*normalRep k 1527=normalRep k 1563 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_1527_19 : a k 19*normalRep k 1527=normalRep k 1564 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_1527 (b : Fin 75) : a k b*normalRep k 1527 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1527_18 k]
      exact normal_mem k 1563
    · rw [extension_1527_19 k]
      exact normal_mem k 1564
  · rw [show a k b*normalRep k 1527=0 from arrow_incompatible k b 11 17 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 1527) h]
    exact Submodule.zero_mem _
lemma extension_1528_60 : a k 60*normalRep k 1528=normalRep k 1565 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_1528_61 : a k 61*normalRep k 1528=0 := by
  change a k 61*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1283 (a k) (relation_zero k) (e k 11)
lemma extension_1528_62 : a k 62*normalRep k 1528=normalRep k 1564 := by
  change a k 62*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1284 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1528 (b : Fin 75) : a k b*normalRep k 1528 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1528_60 k]
      exact normal_mem k 1565
    · rw [extension_1528_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1528_62 k]
      exact normal_mem k 1564
  · rw [show a k b*normalRep k 1528=0 from arrow_incompatible k b 11 40 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 1528) h]
    exact Submodule.zero_mem _
lemma extension_1529_14 : a k 14*normalRep k 1529=normalRep k 1563 := by
  change a k 14*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1285 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1529 (b : Fin 75) : a k b*normalRep k 1529 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1529_14 k]
      exact normal_mem k 1563
  · rw [show a k b*normalRep k 1529=0 from arrow_incompatible k b 11 14 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 1529) h]
    exact Submodule.zero_mem _
lemma extension_1530_63 : a k 63*normalRep k 1530=normalRep k 1566 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1530_64 : a k 64*normalRep k 1530=0 := by
  change a k 64*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1268 (a k) (relation_zero k) (e k 12)
lemma extension_1530_65 : a k 65*normalRep k 1530=0 := by
  change a k 65*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1274 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1530 (b : Fin 75) : a k b*normalRep k 1530 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1530_63 k]
      exact normal_mem k 1566
    · rw [extension_1530_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1530_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1530=0 from arrow_incompatible k b 12 41 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1530) h]
    exact Submodule.zero_mem _
lemma extension_1531_9 : a k 9*normalRep k 1531=normalRep k 1567 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1531 (b : Fin 75) : a k b*normalRep k 1531 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1531_9 k]
      exact normal_mem k 1567
  · rw [show a k b*normalRep k 1531=0 from arrow_incompatible k b 21 9 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1531) h]
    exact Submodule.zero_mem _
lemma extension_1532_52 : a k 52*normalRep k 1532=normalRep k 1567 := by
  change a k 52*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1279 (a k) (relation_zero k) (e k 21)
lemma extension_1532_53 : a k 53*normalRep k 1532=normalRep k 1568 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1532 (b : Fin 75) : a k b*normalRep k 1532 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1532_52 k]
      exact normal_mem k 1567
    · rw [extension_1532_53 k]
      exact normal_mem k 1568
  · rw [show a k b*normalRep k 1532=0 from arrow_incompatible k b 21 37 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1532) h]
    exact Submodule.zero_mem _
lemma extension_1533_4 : a k 4*normalRep k 1533=normalRep k 1568 := by
  change a k 4*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1291 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1533 (b : Fin 75) : a k b*normalRep k 1533 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1533_4 k]
      exact normal_mem k 1568
  · rw [show a k b*normalRep k 1533=0 from arrow_incompatible k b 21 4 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1533) h]
    exact Submodule.zero_mem _
lemma extension_1534_2 : a k 2*normalRep k 1534=normalRep k 1569 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1534 (b : Fin 75) : a k b*normalRep k 1534 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1534_2 k]
      exact normal_mem k 1569
  · rw [show a k b*normalRep k 1534=0 from arrow_incompatible k b 22 2 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1534) h]
    exact Submodule.zero_mem _
lemma extension_1535_41 : a k 41*normalRep k 1535=normalRep k 1570 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1535_42 : a k 42*normalRep k 1535=0 := by
  change a k 42*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1271 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1535 (b : Fin 75) : a k b*normalRep k 1535 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1535_41 k]
      exact normal_mem k 1570
    · rw [extension_1535_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1535=0 from arrow_incompatible k b 24 31 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1535) h]
    exact Submodule.zero_mem _
lemma extension_1536_54 : a k 54*normalRep k 1536=normalRep k 1571 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1536_55 : a k 55*normalRep k 1536=0 := by
  change a k 55*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1272 (a k) (relation_zero k) (e k 24)
lemma extension_1536_56 : a k 56*normalRep k 1536=normalRep k 1570 := by
  change a k 56*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1287 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1536 (b : Fin 75) : a k b*normalRep k 1536 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1536_54 k]
      exact normal_mem k 1571
    · rw [extension_1536_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1536_56 k]
      exact normal_mem k 1570
  · rw [show a k b*normalRep k 1536=0 from arrow_incompatible k b 24 38 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1536) h]
    exact Submodule.zero_mem _
lemma extension_1537_5 : a k 5*normalRep k 1537=normalRep k 1572 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1537 (b : Fin 75) : a k b*normalRep k 1537 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1537_5 k]
      exact normal_mem k 1572
  · rw [show a k b*normalRep k 1537=0 from arrow_incompatible k b 25 5 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1537) h]
    exact Submodule.zero_mem _
lemma extension_1538_33 : a k 33*normalRep k 1538=0 := by
  change a k 33*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1266 (a k) (relation_zero k) (e k 25)
lemma extension_1538_34 : a k 34*normalRep k 1538=normalRep k 1572 := by
  change a k 34*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1289 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1538 (b : Fin 75) : a k b*normalRep k 1538 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1538_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1538_34 k]
      exact normal_mem k 1572
  · rw [show a k b*normalRep k 1538=0 from arrow_incompatible k b 25 26 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1538) h]
    exact Submodule.zero_mem _
lemma arrow_span_1539 (b : Fin 75) : a k b*normalRep k 1539 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1539=0 from arrow_incompatible k b 26 46 [33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1539) h]
    exact Submodule.zero_mem _
lemma extension_1540_20 : a k 20*normalRep k 1540=normalRep k 1573 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1540_21 : a k 21*normalRep k 1540=0 := by
  change a k 21*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1292 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1540 (b : Fin 75) : a k b*normalRep k 1540 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1540_20 k]
      exact normal_mem k 1573
    · rw [extension_1540_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1540=0 from arrow_incompatible k b 27 18 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1540) h]
    exact Submodule.zero_mem _
lemma extension_1541_5 : a k 5*normalRep k 1541=normalRep k 1574 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1541 (b : Fin 75) : a k b*normalRep k 1541 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1541_5 k]
      exact normal_mem k 1574
  · rw [show a k b*normalRep k 1541=0 from arrow_incompatible k b 30 5 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1541) h]
    exact Submodule.zero_mem _
lemma extension_1542_33 : a k 33*normalRep k 1542=0 := by
  change a k 33*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1267 (a k) (relation_zero k) (e k 30)
lemma extension_1542_34 : a k 34*normalRep k 1542=normalRep k 1574 := by
  change a k 34*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1290 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1542 (b : Fin 75) : a k b*normalRep k 1542 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1542_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1542_34 k]
      exact normal_mem k 1574
  · rw [show a k b*normalRep k 1542=0 from arrow_incompatible k b 30 26 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1542) h]
    exact Submodule.zero_mem _
lemma extension_1543_30 : a k 30*normalRep k 1543=normalRep k 1575 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1543_31 : a k 31*normalRep k 1543=0 := by
  change a k 31*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1280 (a k) (relation_zero k) (e k 31)
lemma arrow_span_1543 (b : Fin 75) : a k b*normalRep k 1543 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1543_30 k]
      exact normal_mem k 1575
    · rw [extension_1543_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1543=0 from arrow_incompatible k b 31 24 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1543) h]
    exact Submodule.zero_mem _
lemma extension_1544_2 : a k 2*normalRep k 1544=normalRep k 1576 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1544 (b : Fin 75) : a k b*normalRep k 1544 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1544_2 k]
      exact normal_mem k 1576
  · rw [show a k b*normalRep k 1544=0 from arrow_incompatible k b 32 2 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1544) h]
    exact Submodule.zero_mem _
lemma extension_1545_2 : a k 2*normalRep k 1545=normalRep k 1577 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1545 (b : Fin 75) : a k b*normalRep k 1545 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1545_2 k]
      exact normal_mem k 1577
  · rw [show a k b*normalRep k 1545=0 from arrow_incompatible k b 33 2 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1545) h]
    exact Submodule.zero_mem _
lemma extension_1546_0 : a k 0*normalRep k 1546=normalRep k 1578 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1546 (b : Fin 75) : a k b*normalRep k 1546 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1546_0 k]
      exact normal_mem k 1578
  · rw [show a k b*normalRep k 1546=0 from arrow_incompatible k b 34 0 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1546) h]
    exact Submodule.zero_mem _
lemma arrow_span_1547 (b : Fin 75) : a k b*normalRep k 1547 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1547=0 from arrow_incompatible k b 36 46 [50, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1547) h]
    exact Submodule.zero_mem _
lemma extension_1548_20 : a k 20*normalRep k 1548=normalRep k 1579 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1548_21 : a k 21*normalRep k 1548=0 := by
  change a k 21*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1293 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1548 (b : Fin 75) : a k b*normalRep k 1548 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1548_20 k]
      exact normal_mem k 1579
    · rw [extension_1548_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1548=0 from arrow_incompatible k b 37 18 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1548) h]
    exact Submodule.zero_mem _
lemma extension_1549_30 : a k 30*normalRep k 1549=normalRep k 1580 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1549_31 : a k 31*normalRep k 1549=0 := by
  change a k 31*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1281 (a k) (relation_zero k) (e k 38)
lemma arrow_span_1549 (b : Fin 75) : a k b*normalRep k 1549 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1549_30 k]
      exact normal_mem k 1580
    · rw [extension_1549_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1549=0 from arrow_incompatible k b 38 24 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1549) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
