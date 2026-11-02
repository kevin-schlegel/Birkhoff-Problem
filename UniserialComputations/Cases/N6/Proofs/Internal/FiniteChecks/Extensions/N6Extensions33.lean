import N6NormalData
import N6Reduced22
import N6Reduced23
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_1650_30 : a k 30*normalRep k 1650=normalRep k 1664 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1650_31 : a k 31*normalRep k 1650=0 := by
  change a k 31*walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1365 (a k) (relation_zero k) (e k 42)
lemma arrow_span_1650 (b : Fin 75) : a k b*normalRep k 1650 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1650_30 k]
      exact normal_mem k 1664
    · rw [extension_1650_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1650=0 from arrow_incompatible k b 42 24 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1650) h]
    exact Submodule.zero_mem _
lemma extension_1651_20 : a k 20*normalRep k 1651=normalRep k 1665 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1651_21 : a k 21*normalRep k 1651=0 := by
  change a k 21*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1369 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1651 (b : Fin 75) : a k b*normalRep k 1651 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1651_20 k]
      exact normal_mem k 1665
    · rw [extension_1651_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1651=0 from arrow_incompatible k b 44 18 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1651) h]
    exact Submodule.zero_mem _
lemma extension_1652_41 : a k 41*normalRep k 1652=normalRep k 1666 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_1652_42 : a k 42*normalRep k 1652=0 := by
  change a k 42*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1359 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1652 (b : Fin 75) : a k b*normalRep k 1652 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1652_41 k]
      exact normal_mem k 1666
    · rw [extension_1652_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1652=0 from arrow_incompatible k b 45 31 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 1652) h]
    exact Submodule.zero_mem _
lemma extension_1653_54 : a k 54*normalRep k 1653=normalRep k 1667 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_1653_55 : a k 55*normalRep k 1653=0 := by
  change a k 55*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1360 (a k) (relation_zero k) (e k 45)
lemma extension_1653_56 : a k 56*normalRep k 1653=normalRep k 1666 := by
  change a k 56*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1366 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1653 (b : Fin 75) : a k b*normalRep k 1653 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1653_54 k]
      exact normal_mem k 1667
    · rw [extension_1653_55 k]
      exact Submodule.zero_mem _
    · rw [extension_1653_56 k]
      exact normal_mem k 1666
  · rw [show a k b*normalRep k 1653=0 from arrow_incompatible k b 45 38 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 1653) h]
    exact Submodule.zero_mem _
lemma extension_1654_57 : a k 57*normalRep k 1654=normalRep k 1668 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1654_58 : a k 58*normalRep k 1654=normalRep k 1669 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1654_59 : a k 59*normalRep k 1654=0 := by
  change a k 59*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1375 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1654 (b : Fin 75) : a k b*normalRep k 1654 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1654_57 k]
      exact normal_mem k 1668
    · rw [extension_1654_58 k]
      exact normal_mem k 1669
    · rw [extension_1654_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1654=0 from arrow_incompatible k b 10 39 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1654) h]
    exact Submodule.zero_mem _
lemma extension_1655_1 : a k 1*normalRep k 1655=normalRep k 1669 := by
  change a k 1*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1374 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1655 (b : Fin 75) : a k b*normalRep k 1655 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1655_1 k]
      exact normal_mem k 1669
  · rw [show a k b*normalRep k 1655=0 from arrow_incompatible k b 10 1 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1655) h]
    exact Submodule.zero_mem _
lemma extension_1656_5 : a k 5*normalRep k 1656=normalRep k 1670 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1656 (b : Fin 75) : a k b*normalRep k 1656 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1656_5 k]
      exact normal_mem k 1670
  · rw [show a k b*normalRep k 1656=0 from arrow_incompatible k b 11 5 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1656) h]
    exact Submodule.zero_mem _
lemma extension_1657_33 : a k 33*normalRep k 1657=0 := by
  change a k 33*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1370 (a k) (relation_zero k) (e k 11)
lemma extension_1657_34 : a k 34*normalRep k 1657=normalRep k 1670 := by
  change a k 34*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1378 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1657 (b : Fin 75) : a k b*normalRep k 1657 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1657_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1657_34 k]
      exact normal_mem k 1670
  · rw [show a k b*normalRep k 1657=0 from arrow_incompatible k b 11 26 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1657) h]
    exact Submodule.zero_mem _
lemma arrow_span_1658 (b : Fin 75) : a k b*normalRep k 1658 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1658=0 from arrow_incompatible k b 12 46 [12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1658) h]
    exact Submodule.zero_mem _
lemma extension_1659_63 : a k 63*normalRep k 1659=normalRep k 1671 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1659_64 : a k 64*normalRep k 1659=0 := by
  change a k 64*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1371 (a k) (relation_zero k) (e k 21)
lemma extension_1659_65 : a k 65*normalRep k 1659=0 := by
  change a k 65*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1373 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1659 (b : Fin 75) : a k b*normalRep k 1659 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1659_63 k]
      exact normal_mem k 1671
    · rw [extension_1659_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1659_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1659=0 from arrow_incompatible k b 21 41 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1659) h]
    exact Submodule.zero_mem _
lemma extension_1660_20 : a k 20*normalRep k 1660=normalRep k 1672 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1660_21 : a k 21*normalRep k 1660=0 := by
  change a k 21*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1379 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1660 (b : Fin 75) : a k b*normalRep k 1660 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1660_20 k]
      exact normal_mem k 1672
    · rw [extension_1660_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1660=0 from arrow_incompatible k b 24 18 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1660) h]
    exact Submodule.zero_mem _
lemma extension_1661_0 : a k 0*normalRep k 1661=normalRep k 1673 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1661 (b : Fin 75) : a k b*normalRep k 1661 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1661_0 k]
      exact normal_mem k 1673
  · rw [show a k b*normalRep k 1661=0 from arrow_incompatible k b 25 0 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1661) h]
    exact Submodule.zero_mem _
lemma extension_1662_0 : a k 0*normalRep k 1662=normalRep k 1674 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1662 (b : Fin 75) : a k b*normalRep k 1662 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1662_0 k]
      exact normal_mem k 1674
  · rw [show a k b*normalRep k 1662=0 from arrow_incompatible k b 30 0 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1662) h]
    exact Submodule.zero_mem _
lemma arrow_span_1663 (b : Fin 75) : a k b*normalRep k 1663 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1663=0 from arrow_incompatible k b 40 46 [61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1663) h]
    exact Submodule.zero_mem _
lemma extension_1664_2 : a k 2*normalRep k 1664=normalRep k 1675 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1664 (b : Fin 75) : a k b*normalRep k 1664 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1664_2 k]
      exact normal_mem k 1675
  · rw [show a k b*normalRep k 1664=0 from arrow_incompatible k b 42 2 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1664) h]
    exact Submodule.zero_mem _
lemma extension_1665_30 : a k 30*normalRep k 1665=normalRep k 1676 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1665_31 : a k 31*normalRep k 1665=0 := by
  change a k 31*walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1376 (a k) (relation_zero k) (e k 44)
lemma arrow_span_1665 (b : Fin 75) : a k b*normalRep k 1665 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1665_30 k]
      exact normal_mem k 1676
    · rw [extension_1665_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1665=0 from arrow_incompatible k b 44 24 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1665) h]
    exact Submodule.zero_mem _
lemma extension_1666_43 : a k 43*normalRep k 1666=0 := by
  change a k 43*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1372 (a k) (relation_zero k) (e k 45)
lemma extension_1666_44 : a k 44*normalRep k 1666=normalRep k 1677 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_1666 (b : Fin 75) : a k b*normalRep k 1666 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1666_43 k]
      exact Submodule.zero_mem _
    · rw [extension_1666_44 k]
      exact normal_mem k 1677
  · rw [show a k b*normalRep k 1666=0 from arrow_incompatible k b 45 32 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 1666) h]
    exact Submodule.zero_mem _
lemma extension_1667_15 : a k 15*normalRep k 1667=normalRep k 1678 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_1667_16 : a k 16*normalRep k 1667=normalRep k 1677 := by
  change a k 16*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1377 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1667 (b : Fin 75) : a k b*normalRep k 1667 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1667_15 k]
      exact normal_mem k 1678
    · rw [extension_1667_16 k]
      exact normal_mem k 1677
  · rw [show a k b*normalRep k 1667=0 from arrow_incompatible k b 45 15 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 1667) h]
    exact Submodule.zero_mem _
lemma extension_1668_5 : a k 5*normalRep k 1668=normalRep k 1679 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1668 (b : Fin 75) : a k b*normalRep k 1668 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1668_5 k]
      exact normal_mem k 1679
  · rw [show a k b*normalRep k 1668=0 from arrow_incompatible k b 10 5 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1668) h]
    exact Submodule.zero_mem _
lemma extension_1669_33 : a k 33*normalRep k 1669=0 := by
  change a k 33*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1380 (a k) (relation_zero k) (e k 10)
lemma extension_1669_34 : a k 34*normalRep k 1669=normalRep k 1679 := by
  change a k 34*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1386 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1669 (b : Fin 75) : a k b*normalRep k 1669 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1669_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1669_34 k]
      exact normal_mem k 1679
  · rw [show a k b*normalRep k 1669=0 from arrow_incompatible k b 10 26 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1669) h]
    exact Submodule.zero_mem _
lemma extension_1670_63 : a k 63*normalRep k 1670=normalRep k 1680 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1670_64 : a k 64*normalRep k 1670=0 := by
  change a k 64*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1381 (a k) (relation_zero k) (e k 11)
lemma extension_1670_65 : a k 65*normalRep k 1670=0 := by
  change a k 65*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1382 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1670 (b : Fin 75) : a k b*normalRep k 1670 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1670_63 k]
      exact normal_mem k 1680
    · rw [extension_1670_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1670_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1670=0 from arrow_incompatible k b 11 41 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1670) h]
    exact Submodule.zero_mem _
lemma extension_1671_20 : a k 20*normalRep k 1671=normalRep k 1681 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1671_21 : a k 21*normalRep k 1671=0 := by
  change a k 21*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1387 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1671 (b : Fin 75) : a k b*normalRep k 1671 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1671_20 k]
      exact normal_mem k 1681
    · rw [extension_1671_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1671=0 from arrow_incompatible k b 21 18 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1671) h]
    exact Submodule.zero_mem _
lemma extension_1672_30 : a k 30*normalRep k 1672=normalRep k 1682 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1672_31 : a k 31*normalRep k 1672=0 := by
  change a k 31*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1385 (a k) (relation_zero k) (e k 24)
lemma arrow_span_1672 (b : Fin 75) : a k b*normalRep k 1672 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1672_30 k]
      exact normal_mem k 1682
    · rw [extension_1672_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1672=0 from arrow_incompatible k b 24 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1672) h]
    exact Submodule.zero_mem _
lemma arrow_span_1673 (b : Fin 75) : a k b*normalRep k 1673 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1673=0 from arrow_incompatible k b 25 46 [32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1673) h]
    exact Submodule.zero_mem _
lemma arrow_span_1674 (b : Fin 75) : a k b*normalRep k 1674 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1674=0 from arrow_incompatible k b 30 46 [39, 12, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1674) h]
    exact Submodule.zero_mem _
lemma extension_1675_0 : a k 0*normalRep k 1675=normalRep k 1683 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1675 (b : Fin 75) : a k b*normalRep k 1675 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1675_0 k]
      exact normal_mem k 1683
  · rw [show a k b*normalRep k 1675=0 from arrow_incompatible k b 42 0 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1675) h]
    exact Submodule.zero_mem _
lemma extension_1676_2 : a k 2*normalRep k 1676=normalRep k 1684 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1676 (b : Fin 75) : a k b*normalRep k 1676 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1676_2 k]
      exact normal_mem k 1684
  · rw [show a k b*normalRep k 1676=0 from arrow_incompatible k b 44 2 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1676) h]
    exact Submodule.zero_mem _
lemma extension_1677_57 : a k 57*normalRep k 1677=normalRep k 1685 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_1677_58 : a k 58*normalRep k 1677=normalRep k 1686 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_1677_59 : a k 59*normalRep k 1677=0 := by
  change a k 59*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1384 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1677 (b : Fin 75) : a k b*normalRep k 1677 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1677_57 k]
      exact normal_mem k 1685
    · rw [extension_1677_58 k]
      exact normal_mem k 1686
    · rw [extension_1677_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1677=0 from arrow_incompatible k b 45 39 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 1677) h]
    exact Submodule.zero_mem _
lemma extension_1678_1 : a k 1*normalRep k 1678=normalRep k 1686 := by
  change a k 1*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1383 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1678 (b : Fin 75) : a k b*normalRep k 1678 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1678_1 k]
      exact normal_mem k 1686
  · rw [show a k b*normalRep k 1678=0 from arrow_incompatible k b 45 1 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 1678) h]
    exact Submodule.zero_mem _
lemma extension_1679_63 : a k 63*normalRep k 1679=normalRep k 1687 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1679_64 : a k 64*normalRep k 1679=0 := by
  change a k 64*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1389 (a k) (relation_zero k) (e k 10)
lemma extension_1679_65 : a k 65*normalRep k 1679=0 := by
  change a k 65*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1390 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1679 (b : Fin 75) : a k b*normalRep k 1679 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1679_63 k]
      exact normal_mem k 1687
    · rw [extension_1679_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1679_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1679=0 from arrow_incompatible k b 10 41 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1679) h]
    exact Submodule.zero_mem _
lemma extension_1680_20 : a k 20*normalRep k 1680=normalRep k 1688 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1680_21 : a k 21*normalRep k 1680=0 := by
  change a k 21*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1393 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1680 (b : Fin 75) : a k b*normalRep k 1680 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1680_20 k]
      exact normal_mem k 1688
    · rw [extension_1680_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1680=0 from arrow_incompatible k b 11 18 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1680) h]
    exact Submodule.zero_mem _
lemma extension_1681_30 : a k 30*normalRep k 1681=normalRep k 1689 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1681_31 : a k 31*normalRep k 1681=0 := by
  change a k 31*walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1391 (a k) (relation_zero k) (e k 21)
lemma arrow_span_1681 (b : Fin 75) : a k b*normalRep k 1681 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1681_30 k]
      exact normal_mem k 1689
    · rw [extension_1681_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1681=0 from arrow_incompatible k b 21 24 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1681) h]
    exact Submodule.zero_mem _
lemma extension_1682_2 : a k 2*normalRep k 1682=normalRep k 1690 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1682 (b : Fin 75) : a k b*normalRep k 1682 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1682_2 k]
      exact normal_mem k 1690
  · rw [show a k b*normalRep k 1682=0 from arrow_incompatible k b 24 2 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1682) h]
    exact Submodule.zero_mem _
lemma arrow_span_1683 (b : Fin 75) : a k b*normalRep k 1683 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1683=0 from arrow_incompatible k b 42 46 [67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1683) h]
    exact Submodule.zero_mem _
lemma extension_1684_0 : a k 0*normalRep k 1684=normalRep k 1691 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1684 (b : Fin 75) : a k b*normalRep k 1684 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1684_0 k]
      exact normal_mem k 1691
  · rw [show a k b*normalRep k 1684=0 from arrow_incompatible k b 44 0 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1684) h]
    exact Submodule.zero_mem _
lemma extension_1685_5 : a k 5*normalRep k 1685=normalRep k 1692 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_1685 (b : Fin 75) : a k b*normalRep k 1685 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1685_5 k]
      exact normal_mem k 1692
  · rw [show a k b*normalRep k 1685=0 from arrow_incompatible k b 45 5 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 1685) h]
    exact Submodule.zero_mem _
lemma extension_1686_33 : a k 33*normalRep k 1686=0 := by
  change a k 33*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1388 (a k) (relation_zero k) (e k 45)
lemma extension_1686_34 : a k 34*normalRep k 1686=normalRep k 1692 := by
  change a k 34*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_1392 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1686 (b : Fin 75) : a k b*normalRep k 1686 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1686_33 k]
      exact Submodule.zero_mem _
    · rw [extension_1686_34 k]
      exact normal_mem k 1692
  · rw [show a k b*normalRep k 1686=0 from arrow_incompatible k b 45 26 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 1686) h]
    exact Submodule.zero_mem _
lemma extension_1687_20 : a k 20*normalRep k 1687=normalRep k 1693 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1687_21 : a k 21*normalRep k 1687=0 := by
  change a k 21*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1397 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1687 (b : Fin 75) : a k b*normalRep k 1687 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1687_20 k]
      exact normal_mem k 1693
    · rw [extension_1687_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1687=0 from arrow_incompatible k b 10 18 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1687) h]
    exact Submodule.zero_mem _
lemma extension_1688_30 : a k 30*normalRep k 1688=normalRep k 1694 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1688_31 : a k 31*normalRep k 1688=0 := by
  change a k 31*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1396 (a k) (relation_zero k) (e k 11)
lemma arrow_span_1688 (b : Fin 75) : a k b*normalRep k 1688 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1688_30 k]
      exact normal_mem k 1694
    · rw [extension_1688_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1688=0 from arrow_incompatible k b 11 24 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1688) h]
    exact Submodule.zero_mem _
lemma extension_1689_2 : a k 2*normalRep k 1689=normalRep k 1695 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1689 (b : Fin 75) : a k b*normalRep k 1689 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1689_2 k]
      exact normal_mem k 1695
  · rw [show a k b*normalRep k 1689=0 from arrow_incompatible k b 21 2 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1689) h]
    exact Submodule.zero_mem _
lemma extension_1690_0 : a k 0*normalRep k 1690=normalRep k 1696 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1690 (b : Fin 75) : a k b*normalRep k 1690 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1690_0 k]
      exact normal_mem k 1696
  · rw [show a k b*normalRep k 1690=0 from arrow_incompatible k b 24 0 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1690) h]
    exact Submodule.zero_mem _
lemma arrow_span_1691 (b : Fin 75) : a k b*normalRep k 1691 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1691=0 from arrow_incompatible k b 44 46 [73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1691) h]
    exact Submodule.zero_mem _
lemma extension_1692_63 : a k 63*normalRep k 1692=normalRep k 1697 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_1692_64 : a k 64*normalRep k 1692=0 := by
  change a k 64*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1394 (a k) (relation_zero k) (e k 45)
lemma extension_1692_65 : a k 65*normalRep k 1692=0 := by
  change a k 65*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1395 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1692 (b : Fin 75) : a k b*normalRep k 1692 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_1692_63 k]
      exact normal_mem k 1697
    · rw [extension_1692_64 k]
      exact Submodule.zero_mem _
    · rw [extension_1692_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1692=0 from arrow_incompatible k b 45 41 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 1692) h]
    exact Submodule.zero_mem _
lemma extension_1693_30 : a k 30*normalRep k 1693=normalRep k 1698 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_1693_31 : a k 31*normalRep k 1693=0 := by
  change a k 31*walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1398 (a k) (relation_zero k) (e k 10)
lemma arrow_span_1693 (b : Fin 75) : a k b*normalRep k 1693 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1693_30 k]
      exact normal_mem k 1698
    · rw [extension_1693_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1693=0 from arrow_incompatible k b 10 24 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 1693) h]
    exact Submodule.zero_mem _
lemma extension_1694_2 : a k 2*normalRep k 1694=normalRep k 1699 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1694 (b : Fin 75) : a k b*normalRep k 1694 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1694_2 k]
      exact normal_mem k 1699
  · rw [show a k b*normalRep k 1694=0 from arrow_incompatible k b 11 2 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1694) h]
    exact Submodule.zero_mem _
lemma extension_1695_0 : a k 0*normalRep k 1695=normalRep k 1700 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1695 (b : Fin 75) : a k b*normalRep k 1695 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1695_0 k]
      exact normal_mem k 1700
  · rw [show a k b*normalRep k 1695=0 from arrow_incompatible k b 21 0 [26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1695) h]
    exact Submodule.zero_mem _
lemma arrow_span_1696 (b : Fin 75) : a k b*normalRep k 1696 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 1696=0 from arrow_incompatible k b 24 46 [31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 1696) h]
    exact Submodule.zero_mem _
lemma extension_1697_20 : a k 20*normalRep k 1697=normalRep k 1701 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_1697_21 : a k 21*normalRep k 1697=0 := by
  change a k 21*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_1399 (a k) (relation_zero k) (e k 45)
lemma arrow_span_1697 (b : Fin 75) : a k b*normalRep k 1697 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_1697_20 k]
      exact normal_mem k 1701
    · rw [extension_1697_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 1697=0 from arrow_incompatible k b 45 18 [74, 10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 1697) h]
    exact Submodule.zero_mem _
lemma extension_1698_2 : a k 2*normalRep k 1698=normalRep k 1702 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_1698 (b : Fin 75) : a k b*normalRep k 1698 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1698_2 k]
      exact normal_mem k 1702
  · rw [show a k b*normalRep k 1698=0 from arrow_incompatible k b 10 2 [10, 11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 1698) h]
    exact Submodule.zero_mem _
lemma extension_1699_0 : a k 0*normalRep k 1699=normalRep k 1703 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_1699 (b : Fin 75) : a k b*normalRep k 1699 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1699_0 k]
      exact normal_mem k 1703
  · rw [show a k b*normalRep k 1699=0 from arrow_incompatible k b 11 0 [11, 26, 31, 73, 67, 32, 61, 35, 55, 27, 58, 33, 13, 49, 69, 8, 66, 24, 18, 9, 41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 1699) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
