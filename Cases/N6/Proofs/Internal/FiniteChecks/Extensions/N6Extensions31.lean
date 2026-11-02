import N6NormalData
import N6Reduced21
import N6Reduced22
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_1550_0 : a k 0*normalRep k 1550=normalRep k 1581 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1550 (b : Fin 75) : a k b*normalRep k 1550 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1550_0 k]
      exact normal_mem k 1581
  · rw [show a k b*normalRep k 1550=0 from arrow_incompatible k b 39 0 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1550) h]
    exact Submodule.zero_mem _
lemma extension_1551_63 : a k 63*normalRep k 1551=normalRep k 1582 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1551_64 : a k 64*normalRep k 1551=0 := by
  change a k 64*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1269 (a k) (relation_zero k) (e k 40)
lemma extension_1551_65 : a k 65*normalRep k 1551=0 := by
  change a k 65*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1275 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1551 (b : Fin 75) : a k b*normalRep k 1551 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1551_63 k]
      exact normal_mem k 1582
    · rw [extension_1551_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1551_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1551=0 from arrow_incompatible k b 40 41 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1551) h]
    exact Submodule.zero_mem _
lemma extension_1552_57 : a k 57*normalRep k 1552=normalRep k 1583 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1552_58 : a k 58*normalRep k 1552=normalRep k 1584 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1552_59 : a k 59*normalRep k 1552=0 := by
  change a k 59*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1278 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1552 (b : Fin 75) : a k b*normalRep k 1552 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1552_57 k]
      exact normal_mem k 1583
    · rw [extension_1552_58 k]
      exact normal_mem k 1584
    · rw [extension_1552_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1552=0 from arrow_incompatible k b 42 39 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1552) h]
    exact Submodule.zero_mem _
lemma extension_1553_1 : a k 1*normalRep k 1553=normalRep k 1584 := by
  change a k 1*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1277 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1553 (b : Fin 75) : a k b*normalRep k 1553 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1553_1 k]
      exact normal_mem k 1584
  · rw [show a k b*normalRep k 1553=0 from arrow_incompatible k b 42 1 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1553) h]
    exact Submodule.zero_mem _
lemma extension_1554_43 : a k 43*normalRep k 1554=0 := by
  change a k 43*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1273 (a k) (relation_zero k) (e k 44)
lemma extension_1554_44 : a k 44*normalRep k 1554=normalRep k 1585 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1554 (b : Fin 75) : a k b*normalRep k 1554 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1554_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1554_44 k]
      exact normal_mem k 1585
  · rw [show a k b*normalRep k 1554=0 from arrow_incompatible k b 44 32 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1554) h]
    exact Submodule.zero_mem _
lemma extension_1555_15 : a k 15*normalRep k 1555=normalRep k 1586 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1555_16 : a k 16*normalRep k 1555=normalRep k 1585 := by
  change a k 16*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1288 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1555 (b : Fin 75) : a k b*normalRep k 1555 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1555_15 k]
      exact normal_mem k 1586
    · rw [extension_1555_16 k]
      exact normal_mem k 1585
  · rw [show a k b*normalRep k 1555=0 from arrow_incompatible k b 44 15 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1555) h]
    exact Submodule.zero_mem _
lemma extension_1556_66 : a k 66*normalRep k 1556=normalRep k 1587 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_1556_67 : a k 67*normalRep k 1556=0 := by
  change a k 67*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1276 (a k) (relation_zero k) (e k 45)
lemma extension_1556_68 : a k 68*normalRep k 1556=normalRep k 1588 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_1556 (b : Fin 75) : a k b*normalRep k 1556 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1556_66 k]
      exact normal_mem k 1587
    · rw [extension_1556_67 k]
      exact Submodule.zero_mem _
    · rw [extension_1556_68 k]
      exact normal_mem k 1588
  · rw [show a k b*normalRep k 1556=0 from arrow_incompatible k b 45 42 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8] (normal_endpoints 1556) h]
    exact Submodule.zero_mem _
lemma extension_1557_37 : a k 37*normalRep k 1557=normalRep k 1587 := by
  change a k 37*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1295 (a k) (relation_zero k) (e k 45)
lemma extension_1557_38 : a k 38*normalRep k 1557=normalRep k 1589 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_1557 (b : Fin 75) : a k b*normalRep k 1557 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1557_37 k]
      exact normal_mem k 1587
    · rw [extension_1557_38 k]
      exact normal_mem k 1589
  · rw [show a k b*normalRep k 1557=0 from arrow_incompatible k b 45 29 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72] (normal_endpoints 1557) h]
    exact Submodule.zero_mem _
lemma extension_1558_3 : a k 3*normalRep k 1558=(-normalRep k 1588) := by
  change a k 3*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22]=(-walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1282 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1558 (b : Fin 75) : a k b*normalRep k 1558 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1558_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1588)
  · rw [show a k b*normalRep k 1558=0 from arrow_incompatible k b 45 3 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 34, 63, 21, 70, 22] (normal_endpoints 1558) h]
    exact Submodule.zero_mem _
lemma arrow_span_1559 (b : Fin 75) : a k b*normalRep k 1559 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1559=0 from arrow_incompatible k b 6 46 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1559) h]
    exact Submodule.zero_mem _
lemma extension_1560_18 : a k 18*normalRep k 1560=normalRep k 1590 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_1560_19 : a k 19*normalRep k 1560=normalRep k 1591 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_1560 (b : Fin 75) : a k b*normalRep k 1560 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1560_18 k]
      exact normal_mem k 1590
    · rw [extension_1560_19 k]
      exact normal_mem k 1591
  · rw [show a k b*normalRep k 1560=0 from arrow_incompatible k b 10 17 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 1560) h]
    exact Submodule.zero_mem _
lemma extension_1561_60 : a k 60*normalRep k 1561=normalRep k 1592 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_1561_61 : a k 61*normalRep k 1561=0 := by
  change a k 61*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1310 (a k) (relation_zero k) (e k 10)
lemma extension_1561_62 : a k 62*normalRep k 1561=normalRep k 1591 := by
  change a k 62*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1311 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1561 (b : Fin 75) : a k b*normalRep k 1561 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1561_60 k]
      exact normal_mem k 1592
    · rw [extension_1561_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1561_62 k]
      exact normal_mem k 1591
  · rw [show a k b*normalRep k 1561=0 from arrow_incompatible k b 10 40 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 1561) h]
    exact Submodule.zero_mem _
lemma extension_1562_14 : a k 14*normalRep k 1562=normalRep k 1590 := by
  change a k 14*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1312 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1562 (b : Fin 75) : a k b*normalRep k 1562 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1562_14 k]
      exact normal_mem k 1590
  · rw [show a k b*normalRep k 1562=0 from arrow_incompatible k b 10 14 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 1562) h]
    exact Submodule.zero_mem _
lemma extension_1563_9 : a k 9*normalRep k 1563=normalRep k 1593 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1563 (b : Fin 75) : a k b*normalRep k 1563 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1563_9 k]
      exact normal_mem k 1593
  · rw [show a k b*normalRep k 1563=0 from arrow_incompatible k b 11 9 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1563) h]
    exact Submodule.zero_mem _
lemma extension_1564_52 : a k 52*normalRep k 1564=normalRep k 1593 := by
  change a k 52*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1307 (a k) (relation_zero k) (e k 11)
lemma extension_1564_53 : a k 53*normalRep k 1564=normalRep k 1594 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1564 (b : Fin 75) : a k b*normalRep k 1564 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1564_52 k]
      exact normal_mem k 1593
    · rw [extension_1564_53 k]
      exact normal_mem k 1594
  · rw [show a k b*normalRep k 1564=0 from arrow_incompatible k b 11 37 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1564) h]
    exact Submodule.zero_mem _
lemma extension_1565_4 : a k 4*normalRep k 1565=normalRep k 1594 := by
  change a k 4*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1317 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1565 (b : Fin 75) : a k b*normalRep k 1565 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1565_4 k]
      exact normal_mem k 1594
  · rw [show a k b*normalRep k 1565=0 from arrow_incompatible k b 11 4 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1565) h]
    exact Submodule.zero_mem _
lemma extension_1566_20 : a k 20*normalRep k 1566=normalRep k 1595 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1566_21 : a k 21*normalRep k 1566=0 := by
  change a k 21*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1318 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1566 (b : Fin 75) : a k b*normalRep k 1566 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1566_20 k]
      exact normal_mem k 1595
    · rw [extension_1566_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1566=0 from arrow_incompatible k b 12 18 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1566) h]
    exact Submodule.zero_mem _
lemma extension_1567_41 : a k 41*normalRep k 1567=normalRep k 1596 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1567_42 : a k 42*normalRep k 1567=0 := by
  change a k 42*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1300 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1567 (b : Fin 75) : a k b*normalRep k 1567 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1567_41 k]
      exact normal_mem k 1596
    · rw [extension_1567_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1567=0 from arrow_incompatible k b 21 31 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1567) h]
    exact Submodule.zero_mem _
lemma extension_1568_54 : a k 54*normalRep k 1568=normalRep k 1597 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1568_55 : a k 55*normalRep k 1568=0 := by
  change a k 55*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1301 (a k) (relation_zero k) (e k 21)
lemma extension_1568_56 : a k 56*normalRep k 1568=normalRep k 1596 := by
  change a k 56*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1314 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1568 (b : Fin 75) : a k b*normalRep k 1568 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1568_54 k]
      exact normal_mem k 1597
    · rw [extension_1568_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1568_56 k]
      exact normal_mem k 1596
  · rw [show a k b*normalRep k 1568=0 from arrow_incompatible k b 21 38 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1568) h]
    exact Submodule.zero_mem _
lemma extension_1569_0 : a k 0*normalRep k 1569=normalRep k 1598 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1569 (b : Fin 75) : a k b*normalRep k 1569 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1569_0 k]
      exact normal_mem k 1598
  · rw [show a k b*normalRep k 1569=0 from arrow_incompatible k b 22 0 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1569) h]
    exact Submodule.zero_mem _
lemma extension_1570_43 : a k 43*normalRep k 1570=0 := by
  change a k 43*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1302 (a k) (relation_zero k) (e k 24)
lemma extension_1570_44 : a k 44*normalRep k 1570=normalRep k 1599 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1570 (b : Fin 75) : a k b*normalRep k 1570 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1570_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1570_44 k]
      exact normal_mem k 1599
  · rw [show a k b*normalRep k 1570=0 from arrow_incompatible k b 24 32 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1570) h]
    exact Submodule.zero_mem _
lemma extension_1571_15 : a k 15*normalRep k 1571=normalRep k 1600 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1571_16 : a k 16*normalRep k 1571=normalRep k 1599 := by
  change a k 16*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1315 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1571 (b : Fin 75) : a k b*normalRep k 1571 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1571_15 k]
      exact normal_mem k 1600
    · rw [extension_1571_16 k]
      exact normal_mem k 1599
  · rw [show a k b*normalRep k 1571=0 from arrow_incompatible k b 24 15 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1571) h]
    exact Submodule.zero_mem _
lemma extension_1572_63 : a k 63*normalRep k 1572=normalRep k 1601 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1572_64 : a k 64*normalRep k 1572=0 := by
  change a k 64*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1297 (a k) (relation_zero k) (e k 25)
lemma extension_1572_65 : a k 65*normalRep k 1572=0 := by
  change a k 65*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1303 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1572 (b : Fin 75) : a k b*normalRep k 1572 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1572_63 k]
      exact normal_mem k 1601
    · rw [extension_1572_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1572_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1572=0 from arrow_incompatible k b 25 41 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1572) h]
    exact Submodule.zero_mem _
lemma extension_1573_30 : a k 30*normalRep k 1573=normalRep k 1602 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1573_31 : a k 31*normalRep k 1573=0 := by
  change a k 31*walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1308 (a k) (relation_zero k) (e k 27)
lemma arrow_span_1573 (b : Fin 75) : a k b*normalRep k 1573 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1573_30 k]
      exact normal_mem k 1602
    · rw [extension_1573_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1573=0 from arrow_incompatible k b 27 24 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1573) h]
    exact Submodule.zero_mem _
lemma extension_1574_63 : a k 63*normalRep k 1574=normalRep k 1603 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1574_64 : a k 64*normalRep k 1574=0 := by
  change a k 64*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1298 (a k) (relation_zero k) (e k 30)
lemma extension_1574_65 : a k 65*normalRep k 1574=0 := by
  change a k 65*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1304 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1574 (b : Fin 75) : a k b*normalRep k 1574 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1574_63 k]
      exact normal_mem k 1603
    · rw [extension_1574_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1574_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1574=0 from arrow_incompatible k b 30 41 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1574) h]
    exact Submodule.zero_mem _
lemma extension_1575_2 : a k 2*normalRep k 1575=normalRep k 1604 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1575 (b : Fin 75) : a k b*normalRep k 1575 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1575_2 k]
      exact normal_mem k 1604
  · rw [show a k b*normalRep k 1575=0 from arrow_incompatible k b 31 2 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1575) h]
    exact Submodule.zero_mem _
lemma extension_1576_0 : a k 0*normalRep k 1576=normalRep k 1605 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1576 (b : Fin 75) : a k b*normalRep k 1576 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1576_0 k]
      exact normal_mem k 1605
  · rw [show a k b*normalRep k 1576=0 from arrow_incompatible k b 32 0 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1576) h]
    exact Submodule.zero_mem _
lemma extension_1577_0 : a k 0*normalRep k 1577=normalRep k 1606 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1577 (b : Fin 75) : a k b*normalRep k 1577 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1577_0 k]
      exact normal_mem k 1606
  · rw [show a k b*normalRep k 1577=0 from arrow_incompatible k b 33 0 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1577) h]
    exact Submodule.zero_mem _
lemma arrow_span_1578 (b : Fin 75) : a k b*normalRep k 1578 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1578=0 from arrow_incompatible k b 34 46 [47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1578) h]
    exact Submodule.zero_mem _
lemma extension_1579_30 : a k 30*normalRep k 1579=normalRep k 1607 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1579_31 : a k 31*normalRep k 1579=0 := by
  change a k 31*walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1309 (a k) (relation_zero k) (e k 37)
lemma arrow_span_1579 (b : Fin 75) : a k b*normalRep k 1579 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1579_30 k]
      exact normal_mem k 1607
    · rw [extension_1579_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1579=0 from arrow_incompatible k b 37 24 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1579) h]
    exact Submodule.zero_mem _
lemma extension_1580_2 : a k 2*normalRep k 1580=normalRep k 1608 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1580 (b : Fin 75) : a k b*normalRep k 1580 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1580_2 k]
      exact normal_mem k 1608
  · rw [show a k b*normalRep k 1580=0 from arrow_incompatible k b 38 2 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1580) h]
    exact Submodule.zero_mem _
lemma arrow_span_1581 (b : Fin 75) : a k b*normalRep k 1581 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1581=0 from arrow_incompatible k b 39 46 [58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1581) h]
    exact Submodule.zero_mem _
lemma extension_1582_20 : a k 20*normalRep k 1582=normalRep k 1609 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1582_21 : a k 21*normalRep k 1582=0 := by
  change a k 21*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1319 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1582 (b : Fin 75) : a k b*normalRep k 1582 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1582_20 k]
      exact normal_mem k 1609
    · rw [extension_1582_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1582=0 from arrow_incompatible k b 40 18 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1582) h]
    exact Submodule.zero_mem _
lemma extension_1583_5 : a k 5*normalRep k 1583=normalRep k 1610 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1583 (b : Fin 75) : a k b*normalRep k 1583 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1583_5 k]
      exact normal_mem k 1610
  · rw [show a k b*normalRep k 1583=0 from arrow_incompatible k b 42 5 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1583) h]
    exact Submodule.zero_mem _
lemma extension_1584_33 : a k 33*normalRep k 1584=0 := by
  change a k 33*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1296 (a k) (relation_zero k) (e k 42)
lemma extension_1584_34 : a k 34*normalRep k 1584=normalRep k 1610 := by
  change a k 34*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1316 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1584 (b : Fin 75) : a k b*normalRep k 1584 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1584_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1584_34 k]
      exact normal_mem k 1610
  · rw [show a k b*normalRep k 1584=0 from arrow_incompatible k b 42 26 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1584) h]
    exact Submodule.zero_mem _
lemma extension_1585_57 : a k 57*normalRep k 1585=normalRep k 1611 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1585_58 : a k 58*normalRep k 1585=normalRep k 1612 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1585_59 : a k 59*normalRep k 1585=0 := by
  change a k 59*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1306 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1585 (b : Fin 75) : a k b*normalRep k 1585 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1585_57 k]
      exact normal_mem k 1611
    · rw [extension_1585_58 k]
      exact normal_mem k 1612
    · rw [extension_1585_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1585=0 from arrow_incompatible k b 44 39 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1585) h]
    exact Submodule.zero_mem _
lemma extension_1586_1 : a k 1*normalRep k 1586=normalRep k 1612 := by
  change a k 1*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1305 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1586 (b : Fin 75) : a k b*normalRep k 1586 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1586_1 k]
      exact normal_mem k 1612
  · rw [show a k b*normalRep k 1586=0 from arrow_incompatible k b 44 1 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1586) h]
    exact Submodule.zero_mem _
lemma extension_1587_24 : a k 24*normalRep k 1587=normalRep k 1613 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_1587_25 : a k 25*normalRep k 1587=normalRep k 1614 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_1587 (b : Fin 75) : a k b*normalRep k 1587 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1587_24 k]
      exact normal_mem k 1613
    · rw [extension_1587_25 k]
      exact normal_mem k 1614
  · rw [show a k b*normalRep k 1587=0 from arrow_incompatible k b 45 20 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 1587) h]
    exact Submodule.zero_mem _
lemma extension_1588_39 : a k 39*normalRep k 1588=0 := by
  change a k 39*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1299 (a k) (relation_zero k) (e k 45)
lemma extension_1588_40 : a k 40*normalRep k 1588=(-normalRep k 1614) := by
  change a k 40*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_1320 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1588 (b : Fin 75) : a k b*normalRep k 1588 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1588_39 k]
      exact Submodule.zero_mem _
    · rw [extension_1588_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 1614)
  · rw [show a k b*normalRep k 1588=0 from arrow_incompatible k b 45 30 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 1588) h]
    exact Submodule.zero_mem _
lemma extension_1589_28 : a k 28*normalRep k 1589=normalRep k 1615 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_1589_29 : a k 29*normalRep k 1589=normalRep k 1613 := by
  change a k 29*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1313 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1589 (b : Fin 75) : a k b*normalRep k 1589 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1589_28 k]
      exact normal_mem k 1615
    · rw [extension_1589_29 k]
      exact normal_mem k 1613
  · rw [show a k b*normalRep k 1589=0 from arrow_incompatible k b 45 23 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 1589) h]
    exact Submodule.zero_mem _
lemma extension_1590_9 : a k 9*normalRep k 1590=normalRep k 1616 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1590 (b : Fin 75) : a k b*normalRep k 1590 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1590_9 k]
      exact normal_mem k 1616
  · rw [show a k b*normalRep k 1590=0 from arrow_incompatible k b 10 9 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1590) h]
    exact Submodule.zero_mem _
lemma extension_1591_52 : a k 52*normalRep k 1591=normalRep k 1616 := by
  change a k 52*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1329 (a k) (relation_zero k) (e k 10)
lemma extension_1591_53 : a k 53*normalRep k 1591=normalRep k 1617 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1591 (b : Fin 75) : a k b*normalRep k 1591 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1591_52 k]
      exact normal_mem k 1616
    · rw [extension_1591_53 k]
      exact normal_mem k 1617
  · rw [show a k b*normalRep k 1591=0 from arrow_incompatible k b 10 37 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1591) h]
    exact Submodule.zero_mem _
lemma extension_1592_4 : a k 4*normalRep k 1592=normalRep k 1617 := by
  change a k 4*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1338 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1592 (b : Fin 75) : a k b*normalRep k 1592 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1592_4 k]
      exact normal_mem k 1617
  · rw [show a k b*normalRep k 1592=0 from arrow_incompatible k b 10 4 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1592) h]
    exact Submodule.zero_mem _
lemma extension_1593_41 : a k 41*normalRep k 1593=normalRep k 1618 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1593_42 : a k 42*normalRep k 1593=0 := by
  change a k 42*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1323 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1593 (b : Fin 75) : a k b*normalRep k 1593 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1593_41 k]
      exact normal_mem k 1618
    · rw [extension_1593_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1593=0 from arrow_incompatible k b 11 31 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1593) h]
    exact Submodule.zero_mem _
lemma extension_1594_54 : a k 54*normalRep k 1594=normalRep k 1619 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1594_55 : a k 55*normalRep k 1594=0 := by
  change a k 55*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1324 (a k) (relation_zero k) (e k 11)
lemma extension_1594_56 : a k 56*normalRep k 1594=normalRep k 1618 := by
  change a k 56*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1335 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1594 (b : Fin 75) : a k b*normalRep k 1594 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1594_54 k]
      exact normal_mem k 1619
    · rw [extension_1594_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1594_56 k]
      exact normal_mem k 1618
  · rw [show a k b*normalRep k 1594=0 from arrow_incompatible k b 11 38 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1594) h]
    exact Submodule.zero_mem _
lemma extension_1595_30 : a k 30*normalRep k 1595=normalRep k 1620 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1595_31 : a k 31*normalRep k 1595=0 := by
  change a k 31*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1330 (a k) (relation_zero k) (e k 12)
lemma arrow_span_1595 (b : Fin 75) : a k b*normalRep k 1595 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1595_30 k]
      exact normal_mem k 1620
    · rw [extension_1595_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1595=0 from arrow_incompatible k b 12 24 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1595) h]
    exact Submodule.zero_mem _
lemma extension_1596_43 : a k 43*normalRep k 1596=0 := by
  change a k 43*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1325 (a k) (relation_zero k) (e k 21)
lemma extension_1596_44 : a k 44*normalRep k 1596=normalRep k 1621 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1596 (b : Fin 75) : a k b*normalRep k 1596 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1596_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1596_44 k]
      exact normal_mem k 1621
  · rw [show a k b*normalRep k 1596=0 from arrow_incompatible k b 21 32 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1596) h]
    exact Submodule.zero_mem _
lemma extension_1597_15 : a k 15*normalRep k 1597=normalRep k 1622 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1597_16 : a k 16*normalRep k 1597=normalRep k 1621 := by
  change a k 16*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1336 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1597 (b : Fin 75) : a k b*normalRep k 1597 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1597_15 k]
      exact normal_mem k 1622
    · rw [extension_1597_16 k]
      exact normal_mem k 1621
  · rw [show a k b*normalRep k 1597=0 from arrow_incompatible k b 21 15 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1597) h]
    exact Submodule.zero_mem _
lemma arrow_span_1598 (b : Fin 75) : a k b*normalRep k 1598 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1598=0 from arrow_incompatible k b 22 46 [27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1598) h]
    exact Submodule.zero_mem _
lemma extension_1599_57 : a k 57*normalRep k 1599=normalRep k 1623 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1599_58 : a k 58*normalRep k 1599=normalRep k 1624 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1599_59 : a k 59*normalRep k 1599=0 := by
  change a k 59*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1328 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1599 (b : Fin 75) : a k b*normalRep k 1599 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1599_57 k]
      exact normal_mem k 1623
    · rw [extension_1599_58 k]
      exact normal_mem k 1624
    · rw [extension_1599_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1599=0 from arrow_incompatible k b 24 39 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1599) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
