import N6NormalData
import N6Reduced22
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_1600_1 : a k 1*normalRep k 1600=normalRep k 1624 := by
  change a k 1*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1327 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1600 (b : Fin 75) : a k b*normalRep k 1600 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1600_1 k]
      exact normal_mem k 1624
  · rw [show a k b*normalRep k 1600=0 from arrow_incompatible k b 24 1 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1600) h]
    exact Submodule.zero_mem _
lemma extension_1601_20 : a k 20*normalRep k 1601=normalRep k 1625 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1601_21 : a k 21*normalRep k 1601=0 := by
  change a k 21*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1339 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1601 (b : Fin 75) : a k b*normalRep k 1601 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1601_20 k]
      exact normal_mem k 1625
    · rw [extension_1601_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1601=0 from arrow_incompatible k b 25 18 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1601) h]
    exact Submodule.zero_mem _
lemma extension_1602_2 : a k 2*normalRep k 1602=normalRep k 1626 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1602 (b : Fin 75) : a k b*normalRep k 1602 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1602_2 k]
      exact normal_mem k 1626
  · rw [show a k b*normalRep k 1602=0 from arrow_incompatible k b 27 2 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1602) h]
    exact Submodule.zero_mem _
lemma extension_1603_20 : a k 20*normalRep k 1603=normalRep k 1627 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1603_21 : a k 21*normalRep k 1603=0 := by
  change a k 21*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1340 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1603 (b : Fin 75) : a k b*normalRep k 1603 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1603_20 k]
      exact normal_mem k 1627
    · rw [extension_1603_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1603=0 from arrow_incompatible k b 30 18 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1603) h]
    exact Submodule.zero_mem _
lemma extension_1604_0 : a k 0*normalRep k 1604=normalRep k 1628 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1604 (b : Fin 75) : a k b*normalRep k 1604 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1604_0 k]
      exact normal_mem k 1628
  · rw [show a k b*normalRep k 1604=0 from arrow_incompatible k b 31 0 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1604) h]
    exact Submodule.zero_mem _
lemma arrow_span_1605 (b : Fin 75) : a k b*normalRep k 1605 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1605=0 from arrow_incompatible k b 32 46 [43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1605) h]
    exact Submodule.zero_mem _
lemma arrow_span_1606 (b : Fin 75) : a k b*normalRep k 1606 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1606=0 from arrow_incompatible k b 33 46 [45, 6, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1606) h]
    exact Submodule.zero_mem _
lemma extension_1607_2 : a k 2*normalRep k 1607=normalRep k 1629 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1607 (b : Fin 75) : a k b*normalRep k 1607 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1607_2 k]
      exact normal_mem k 1629
  · rw [show a k b*normalRep k 1607=0 from arrow_incompatible k b 37 2 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1607) h]
    exact Submodule.zero_mem _
lemma extension_1608_0 : a k 0*normalRep k 1608=normalRep k 1630 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1608 (b : Fin 75) : a k b*normalRep k 1608 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1608_0 k]
      exact normal_mem k 1630
  · rw [show a k b*normalRep k 1608=0 from arrow_incompatible k b 38 0 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1608) h]
    exact Submodule.zero_mem _
lemma extension_1609_30 : a k 30*normalRep k 1609=normalRep k 1631 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1609_31 : a k 31*normalRep k 1609=0 := by
  change a k 31*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1331 (a k) (relation_zero k) (e k 40)
lemma arrow_span_1609 (b : Fin 75) : a k b*normalRep k 1609 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1609_30 k]
      exact normal_mem k 1631
    · rw [extension_1609_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1609=0 from arrow_incompatible k b 40 24 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1609) h]
    exact Submodule.zero_mem _
lemma extension_1610_63 : a k 63*normalRep k 1610=normalRep k 1632 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1610_64 : a k 64*normalRep k 1610=0 := by
  change a k 64*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1322 (a k) (relation_zero k) (e k 42)
lemma extension_1610_65 : a k 65*normalRep k 1610=0 := by
  change a k 65*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1326 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1610 (b : Fin 75) : a k b*normalRep k 1610 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1610_63 k]
      exact normal_mem k 1632
    · rw [extension_1610_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1610_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1610=0 from arrow_incompatible k b 42 41 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1610) h]
    exact Submodule.zero_mem _
lemma extension_1611_5 : a k 5*normalRep k 1611=normalRep k 1633 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1611 (b : Fin 75) : a k b*normalRep k 1611 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1611_5 k]
      exact normal_mem k 1633
  · rw [show a k b*normalRep k 1611=0 from arrow_incompatible k b 44 5 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1611) h]
    exact Submodule.zero_mem _
lemma extension_1612_33 : a k 33*normalRep k 1612=0 := by
  change a k 33*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1321 (a k) (relation_zero k) (e k 44)
lemma extension_1612_34 : a k 34*normalRep k 1612=normalRep k 1633 := by
  change a k 34*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1337 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1612 (b : Fin 75) : a k b*normalRep k 1612 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1612_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1612_34 k]
      exact normal_mem k 1633
  · rw [show a k b*normalRep k 1612=0 from arrow_incompatible k b 44 26 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1612) h]
    exact Submodule.zero_mem _
lemma extension_1613_18 : a k 18*normalRep k 1613=normalRep k 1634 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_1613_19 : a k 19*normalRep k 1613=normalRep k 1635 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_1613 (b : Fin 75) : a k b*normalRep k 1613 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1613_18 k]
      exact normal_mem k 1634
    · rw [extension_1613_19 k]
      exact normal_mem k 1635
  · rw [show a k b*normalRep k 1613=0 from arrow_incompatible k b 45 17 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 1613) h]
    exact Submodule.zero_mem _
lemma extension_1614_60 : a k 60*normalRep k 1614=normalRep k 1636 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_1614_61 : a k 61*normalRep k 1614=0 := by
  change a k 61*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1332 (a k) (relation_zero k) (e k 45)
lemma extension_1614_62 : a k 62*normalRep k 1614=normalRep k 1635 := by
  change a k 62*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1333 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1614 (b : Fin 75) : a k b*normalRep k 1614 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1614_60 k]
      exact normal_mem k 1636
    · rw [extension_1614_61 k]
      exact Submodule.zero_mem _
    · rw [extension_1614_62 k]
      exact normal_mem k 1635
  · rw [show a k b*normalRep k 1614=0 from arrow_incompatible k b 45 40 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 1614) h]
    exact Submodule.zero_mem _
lemma extension_1615_14 : a k 14*normalRep k 1615=normalRep k 1634 := by
  change a k 14*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1334 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1615 (b : Fin 75) : a k b*normalRep k 1615 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1615_14 k]
      exact normal_mem k 1634
  · rw [show a k b*normalRep k 1615=0 from arrow_incompatible k b 45 14 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 1615) h]
    exact Submodule.zero_mem _
lemma extension_1616_41 : a k 41*normalRep k 1616=normalRep k 1637 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1616_42 : a k 42*normalRep k 1616=0 := by
  change a k 42*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1343 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1616 (b : Fin 75) : a k b*normalRep k 1616 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1616_41 k]
      exact normal_mem k 1637
    · rw [extension_1616_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1616=0 from arrow_incompatible k b 10 31 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1616) h]
    exact Submodule.zero_mem _
lemma extension_1617_54 : a k 54*normalRep k 1617=normalRep k 1638 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1617_55 : a k 55*normalRep k 1617=0 := by
  change a k 55*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1344 (a k) (relation_zero k) (e k 10)
lemma extension_1617_56 : a k 56*normalRep k 1617=normalRep k 1637 := by
  change a k 56*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1352 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1617 (b : Fin 75) : a k b*normalRep k 1617 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1617_54 k]
      exact normal_mem k 1638
    · rw [extension_1617_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1617_56 k]
      exact normal_mem k 1637
  · rw [show a k b*normalRep k 1617=0 from arrow_incompatible k b 10 38 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1617) h]
    exact Submodule.zero_mem _
lemma extension_1618_43 : a k 43*normalRep k 1618=0 := by
  change a k 43*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1345 (a k) (relation_zero k) (e k 11)
lemma extension_1618_44 : a k 44*normalRep k 1618=normalRep k 1639 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1618 (b : Fin 75) : a k b*normalRep k 1618 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1618_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1618_44 k]
      exact normal_mem k 1639
  · rw [show a k b*normalRep k 1618=0 from arrow_incompatible k b 11 32 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1618) h]
    exact Submodule.zero_mem _
lemma extension_1619_15 : a k 15*normalRep k 1619=normalRep k 1640 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1619_16 : a k 16*normalRep k 1619=normalRep k 1639 := by
  change a k 16*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1353 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1619 (b : Fin 75) : a k b*normalRep k 1619 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1619_15 k]
      exact normal_mem k 1640
    · rw [extension_1619_16 k]
      exact normal_mem k 1639
  · rw [show a k b*normalRep k 1619=0 from arrow_incompatible k b 11 15 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1619) h]
    exact Submodule.zero_mem _
lemma extension_1620_2 : a k 2*normalRep k 1620=normalRep k 1641 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1620 (b : Fin 75) : a k b*normalRep k 1620 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1620_2 k]
      exact normal_mem k 1641
  · rw [show a k b*normalRep k 1620=0 from arrow_incompatible k b 12 2 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1620) h]
    exact Submodule.zero_mem _
lemma extension_1621_57 : a k 57*normalRep k 1621=normalRep k 1642 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1621_58 : a k 58*normalRep k 1621=normalRep k 1643 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1621_59 : a k 59*normalRep k 1621=0 := by
  change a k 59*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1348 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1621 (b : Fin 75) : a k b*normalRep k 1621 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1621_57 k]
      exact normal_mem k 1642
    · rw [extension_1621_58 k]
      exact normal_mem k 1643
    · rw [extension_1621_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1621=0 from arrow_incompatible k b 21 39 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1621) h]
    exact Submodule.zero_mem _
lemma extension_1622_1 : a k 1*normalRep k 1622=normalRep k 1643 := by
  change a k 1*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1347 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1622 (b : Fin 75) : a k b*normalRep k 1622 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1622_1 k]
      exact normal_mem k 1643
  · rw [show a k b*normalRep k 1622=0 from arrow_incompatible k b 21 1 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1622) h]
    exact Submodule.zero_mem _
lemma extension_1623_5 : a k 5*normalRep k 1623=normalRep k 1644 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1623 (b : Fin 75) : a k b*normalRep k 1623 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1623_5 k]
      exact normal_mem k 1644
  · rw [show a k b*normalRep k 1623=0 from arrow_incompatible k b 24 5 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1623) h]
    exact Submodule.zero_mem _
lemma extension_1624_33 : a k 33*normalRep k 1624=0 := by
  change a k 33*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1341 (a k) (relation_zero k) (e k 24)
lemma extension_1624_34 : a k 34*normalRep k 1624=normalRep k 1644 := by
  change a k 34*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1354 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1624 (b : Fin 75) : a k b*normalRep k 1624 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1624_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1624_34 k]
      exact normal_mem k 1644
  · rw [show a k b*normalRep k 1624=0 from arrow_incompatible k b 24 26 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1624) h]
    exact Submodule.zero_mem _
lemma extension_1625_30 : a k 30*normalRep k 1625=normalRep k 1645 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1625_31 : a k 31*normalRep k 1625=0 := by
  change a k 31*walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1350 (a k) (relation_zero k) (e k 25)
lemma arrow_span_1625 (b : Fin 75) : a k b*normalRep k 1625 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1625_30 k]
      exact normal_mem k 1645
    · rw [extension_1625_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1625=0 from arrow_incompatible k b 25 24 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1625) h]
    exact Submodule.zero_mem _
lemma extension_1626_0 : a k 0*normalRep k 1626=normalRep k 1646 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1626 (b : Fin 75) : a k b*normalRep k 1626 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1626_0 k]
      exact normal_mem k 1646
  · rw [show a k b*normalRep k 1626=0 from arrow_incompatible k b 27 0 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1626) h]
    exact Submodule.zero_mem _
lemma extension_1627_30 : a k 30*normalRep k 1627=normalRep k 1647 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1627_31 : a k 31*normalRep k 1627=0 := by
  change a k 31*walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1351 (a k) (relation_zero k) (e k 30)
lemma arrow_span_1627 (b : Fin 75) : a k b*normalRep k 1627 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1627_30 k]
      exact normal_mem k 1647
    · rw [extension_1627_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1627=0 from arrow_incompatible k b 30 24 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1627) h]
    exact Submodule.zero_mem _
lemma arrow_span_1628 (b : Fin 75) : a k b*normalRep k 1628 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1628=0 from arrow_incompatible k b 31 46 [41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1628) h]
    exact Submodule.zero_mem _
lemma extension_1629_0 : a k 0*normalRep k 1629=normalRep k 1648 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1629 (b : Fin 75) : a k b*normalRep k 1629 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1629_0 k]
      exact normal_mem k 1648
  · rw [show a k b*normalRep k 1629=0 from arrow_incompatible k b 37 0 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1629) h]
    exact Submodule.zero_mem _
lemma arrow_span_1630 (b : Fin 75) : a k b*normalRep k 1630 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1630=0 from arrow_incompatible k b 38 46 [55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1630) h]
    exact Submodule.zero_mem _
lemma extension_1631_2 : a k 2*normalRep k 1631=normalRep k 1649 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1631 (b : Fin 75) : a k b*normalRep k 1631 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1631_2 k]
      exact normal_mem k 1649
  · rw [show a k b*normalRep k 1631=0 from arrow_incompatible k b 40 2 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1631) h]
    exact Submodule.zero_mem _
lemma extension_1632_20 : a k 20*normalRep k 1632=normalRep k 1650 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1632_21 : a k 21*normalRep k 1632=0 := by
  change a k 21*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1356 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1632 (b : Fin 75) : a k b*normalRep k 1632 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1632_20 k]
      exact normal_mem k 1650
    · rw [extension_1632_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1632=0 from arrow_incompatible k b 42 18 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1632) h]
    exact Submodule.zero_mem _
lemma extension_1633_63 : a k 63*normalRep k 1633=normalRep k 1651 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1633_64 : a k 64*normalRep k 1633=0 := by
  change a k 64*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1342 (a k) (relation_zero k) (e k 44)
lemma extension_1633_65 : a k 65*normalRep k 1633=0 := by
  change a k 65*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1346 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1633 (b : Fin 75) : a k b*normalRep k 1633 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1633_63 k]
      exact normal_mem k 1651
    · rw [extension_1633_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1633_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1633=0 from arrow_incompatible k b 44 41 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1633) h]
    exact Submodule.zero_mem _
lemma extension_1634_9 : a k 9*normalRep k 1634=normalRep k 1652 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_1634 (b : Fin 75) : a k b*normalRep k 1634 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1634_9 k]
      exact normal_mem k 1652
  · rw [show a k b*normalRep k 1634=0 from arrow_incompatible k b 45 9 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 1634) h]
    exact Submodule.zero_mem _
lemma extension_1635_52 : a k 52*normalRep k 1635=normalRep k 1652 := by
  change a k 52*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1349 (a k) (relation_zero k) (e k 45)
lemma extension_1635_53 : a k 53*normalRep k 1635=normalRep k 1653 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_1635 (b : Fin 75) : a k b*normalRep k 1635 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1635_52 k]
      exact normal_mem k 1652
    · rw [extension_1635_53 k]
      exact normal_mem k 1653
  · rw [show a k b*normalRep k 1635=0 from arrow_incompatible k b 45 37 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 1635) h]
    exact Submodule.zero_mem _
lemma extension_1636_4 : a k 4*normalRep k 1636=normalRep k 1653 := by
  change a k 4*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1355 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1636 (b : Fin 75) : a k b*normalRep k 1636 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1636_4 k]
      exact normal_mem k 1653
  · rw [show a k b*normalRep k 1636=0 from arrow_incompatible k b 45 4 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 1636) h]
    exact Submodule.zero_mem _
lemma extension_1637_43 : a k 43*normalRep k 1637=0 := by
  change a k 43*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1361 (a k) (relation_zero k) (e k 10)
lemma extension_1637_44 : a k 44*normalRep k 1637=normalRep k 1654 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1637 (b : Fin 75) : a k b*normalRep k 1637 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1637_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1637_44 k]
      exact normal_mem k 1654
  · rw [show a k b*normalRep k 1637=0 from arrow_incompatible k b 10 32 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1637) h]
    exact Submodule.zero_mem _
lemma extension_1638_15 : a k 15*normalRep k 1638=normalRep k 1655 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1638_16 : a k 16*normalRep k 1638=normalRep k 1654 := by
  change a k 16*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1367 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1638 (b : Fin 75) : a k b*normalRep k 1638 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1638_15 k]
      exact normal_mem k 1655
    · rw [extension_1638_16 k]
      exact normal_mem k 1654
  · rw [show a k b*normalRep k 1638=0 from arrow_incompatible k b 10 15 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1638) h]
    exact Submodule.zero_mem _
lemma extension_1639_57 : a k 57*normalRep k 1639=normalRep k 1656 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1639_58 : a k 58*normalRep k 1639=normalRep k 1657 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1639_59 : a k 59*normalRep k 1639=0 := by
  change a k 59*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1364 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1639 (b : Fin 75) : a k b*normalRep k 1639 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1639_57 k]
      exact normal_mem k 1656
    · rw [extension_1639_58 k]
      exact normal_mem k 1657
    · rw [extension_1639_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1639=0 from arrow_incompatible k b 11 39 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1639) h]
    exact Submodule.zero_mem _
lemma extension_1640_1 : a k 1*normalRep k 1640=normalRep k 1657 := by
  change a k 1*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1363 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1640 (b : Fin 75) : a k b*normalRep k 1640 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1640_1 k]
      exact normal_mem k 1657
  · rw [show a k b*normalRep k 1640=0 from arrow_incompatible k b 11 1 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1640) h]
    exact Submodule.zero_mem _
lemma extension_1641_0 : a k 0*normalRep k 1641=normalRep k 1658 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1641 (b : Fin 75) : a k b*normalRep k 1641 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1641_0 k]
      exact normal_mem k 1658
  · rw [show a k b*normalRep k 1641=0 from arrow_incompatible k b 12 0 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1641) h]
    exact Submodule.zero_mem _
lemma extension_1642_5 : a k 5*normalRep k 1642=normalRep k 1659 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1642 (b : Fin 75) : a k b*normalRep k 1642 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1642_5 k]
      exact normal_mem k 1659
  · rw [show a k b*normalRep k 1642=0 from arrow_incompatible k b 21 5 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1642) h]
    exact Submodule.zero_mem _
lemma extension_1643_33 : a k 33*normalRep k 1643=0 := by
  change a k 33*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1357 (a k) (relation_zero k) (e k 21)
lemma extension_1643_34 : a k 34*normalRep k 1643=normalRep k 1659 := by
  change a k 34*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1368 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1643 (b : Fin 75) : a k b*normalRep k 1643 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1643_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1643_34 k]
      exact normal_mem k 1659
  · rw [show a k b*normalRep k 1643=0 from arrow_incompatible k b 21 26 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1643) h]
    exact Submodule.zero_mem _
lemma extension_1644_63 : a k 63*normalRep k 1644=normalRep k 1660 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1644_64 : a k 64*normalRep k 1644=0 := by
  change a k 64*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1358 (a k) (relation_zero k) (e k 24)
lemma extension_1644_65 : a k 65*normalRep k 1644=0 := by
  change a k 65*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1362 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1644 (b : Fin 75) : a k b*normalRep k 1644 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1644_63 k]
      exact normal_mem k 1660
    · rw [extension_1644_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1644_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1644=0 from arrow_incompatible k b 24 41 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1644) h]
    exact Submodule.zero_mem _
lemma extension_1645_2 : a k 2*normalRep k 1645=normalRep k 1661 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1645 (b : Fin 75) : a k b*normalRep k 1645 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1645_2 k]
      exact normal_mem k 1661
  · rw [show a k b*normalRep k 1645=0 from arrow_incompatible k b 25 2 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1645) h]
    exact Submodule.zero_mem _
lemma arrow_span_1646 (b : Fin 75) : a k b*normalRep k 1646 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1646=0 from arrow_incompatible k b 27 46 [35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1646) h]
    exact Submodule.zero_mem _
lemma extension_1647_2 : a k 2*normalRep k 1647=normalRep k 1662 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1647 (b : Fin 75) : a k b*normalRep k 1647 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1647_2 k]
      exact normal_mem k 1662
  · rw [show a k b*normalRep k 1647=0 from arrow_incompatible k b 30 2 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1647) h]
    exact Submodule.zero_mem _
lemma arrow_span_1648 (b : Fin 75) : a k b*normalRep k 1648 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1648=0 from arrow_incompatible k b 37 46 [52, 41, 43, 47, 7, 17, 21, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1648) h]
    exact Submodule.zero_mem _
lemma extension_1649_0 : a k 0*normalRep k 1649=normalRep k 1663 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1649 (b : Fin 75) : a k b*normalRep k 1649 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1649_0 k]
      exact normal_mem k 1663
  · rw [show a k b*normalRep k 1649=0 from arrow_incompatible k b 40 0 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1649) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
