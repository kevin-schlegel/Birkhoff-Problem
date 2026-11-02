import N6NormalData
import N6Reduced7
import N6Reduced8
import N6Reduced9
import N6Reduced10
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_650_49 : a k 49*normalRep k 650=(-normalRep k 757) + normalRep k 758 := by
  change a k 49*walk k 37 [52, 41, 43, 48, 51, 65]=(-walk k 37 [52, 41, 43, 47, 7, 17, 21]) + walk k 37 [52, 41, 43, 48, 51, 64, 36]
  rw [← walk_snoc]
  exact Universal.mul_reduced_506 (a k) (relation_zero k) (e k 37)
lemma arrow_span_650 (b : Fin 75) : a k b*normalRep k 650 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_650_49 k]
      exact (normalSpan k).add_mem ((normalSpan k).smul_mem (-1:k) (normal_mem k 757)) (normal_mem k 758)
  · rw [show a k b*normalRep k 650=0 from arrow_incompatible k b 37 35 [52, 41, 43, 48, 51, 65] (normal_endpoints 650) h]
    exact Submodule.zero_mem _
lemma extension_651_20 : a k 20*normalRep k 651=normalRep k 759 := by
  exact (walk_snoc k 37 [52, 41, 44, 57, 5, 63] 20).symm
lemma extension_651_21 : a k 21*normalRep k 651=0 := by
  change a k 21*walk k 37 [52, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_507 (a k) (relation_zero k) (e k 37)
lemma arrow_span_651 (b : Fin 75) : a k b*normalRep k 651 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_651_20 k]
      exact normal_mem k 759
    · rw [extension_651_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 651=0 from arrow_incompatible k b 37 18 [52, 41, 44, 57, 5, 63] (normal_endpoints 651) h]
    exact Submodule.zero_mem _
lemma extension_652_30 : a k 30*normalRep k 652=normalRep k 760 := by
  exact (walk_snoc k 38 [54, 15, 1, 34, 63, 20] 30).symm
lemma extension_652_31 : a k 31*normalRep k 652=0 := by
  change a k 31*walk k 38 [54, 15, 1, 34, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_454 (a k) (relation_zero k) (e k 38)
lemma arrow_span_652 (b : Fin 75) : a k b*normalRep k 652 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_652_30 k]
      exact normal_mem k 760
    · rw [extension_652_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 652=0 from arrow_incompatible k b 38 24 [54, 15, 1, 34, 63, 20] (normal_endpoints 652) h]
    exact Submodule.zero_mem _
lemma extension_653_69 : a k 69*normalRep k 653=normalRep k 761 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49] 69).symm
lemma extension_653_70 : a k 70*normalRep k 653=0 := by
  change a k 70*walk k 38 [55, 27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_484 (a k) (relation_zero k) (e k 38)
lemma extension_653_71 : a k 71*normalRep k 653=normalRep k 762 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49] 71).symm
lemma arrow_span_653 (b : Fin 75) : a k b*normalRep k 653 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_653_69 k]
      exact normal_mem k 761
    · rw [extension_653_70 k]
      exact Submodule.zero_mem _
    · rw [extension_653_71 k]
      exact normal_mem k 762
  · rw [show a k b*normalRep k 653=0 from arrow_incompatible k b 38 43 [55, 27, 58, 33, 13, 49] (normal_endpoints 653) h]
    exact Submodule.zero_mem _
lemma extension_654_69 : a k 69*normalRep k 654=(-normalRep k 761) := by
  change a k 69*walk k 38 [55, 27, 58, 34, 63, 21]=(-walk k 38 [55, 27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_474 (a k) (relation_zero k) (e k 38)
lemma extension_654_70 : a k 70*normalRep k 654=normalRep k 763 := by
  exact (walk_snoc k 38 [55, 27, 58, 34, 63, 21] 70).symm
lemma extension_654_71 : a k 71*normalRep k 654=0 := by
  change a k 71*walk k 38 [55, 27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_456 (a k) (relation_zero k) (e k 38)
lemma arrow_span_654 (b : Fin 75) : a k b*normalRep k 654 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_654_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 761)
    · rw [extension_654_70 k]
      exact normal_mem k 763
    · rw [extension_654_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 654=0 from arrow_incompatible k b 38 43 [55, 27, 58, 34, 63, 21] (normal_endpoints 654) h]
    exact Submodule.zero_mem _
lemma extension_655_0 : a k 0*normalRep k 655=normalRep k 764 := by
  exact (walk_snoc k 39 [57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_655 (b : Fin 75) : a k b*normalRep k 655 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_655_0 k]
      exact normal_mem k 764
  · rw [show a k b*normalRep k 655=0 from arrow_incompatible k b 39 0 [57, 5, 63, 20, 30, 2] (normal_endpoints 655) h]
    exact Submodule.zero_mem _
lemma extension_656_66 : a k 66*normalRep k 656=normalRep k 765 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8] 66).symm
lemma extension_656_67 : a k 67*normalRep k 656=0 := by
  change a k 67*walk k 39 [58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_440 (a k) (relation_zero k) (e k 39)
lemma extension_656_68 : a k 68*normalRep k 656=normalRep k 766 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_656 (b : Fin 75) : a k b*normalRep k 656 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_656_66 k]
      exact normal_mem k 765
    · rw [extension_656_67 k]
      exact Submodule.zero_mem _
    · rw [extension_656_68 k]
      exact normal_mem k 766
  · rw [show a k b*normalRep k 656=0 from arrow_incompatible k b 39 42 [58, 33, 13, 49, 69, 8] (normal_endpoints 656) h]
    exact Submodule.zero_mem _
lemma extension_657_37 : a k 37*normalRep k 657=normalRep k 765 := by
  change a k 37*walk k 39 [58, 33, 13, 49, 71, 72]=walk k 39 [58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_519 (a k) (relation_zero k) (e k 39)
lemma extension_657_38 : a k 38*normalRep k 657=normalRep k 767 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_657 (b : Fin 75) : a k b*normalRep k 657 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_657_37 k]
      exact normal_mem k 765
    · rw [extension_657_38 k]
      exact normal_mem k 767
  · rw [show a k b*normalRep k 657=0 from arrow_incompatible k b 39 29 [58, 33, 13, 49, 71, 72] (normal_endpoints 657) h]
    exact Submodule.zero_mem _
lemma extension_658_3 : a k 3*normalRep k 658=(-normalRep k 766) := by
  change a k 3*walk k 39 [58, 34, 63, 21, 70, 22]=(-walk k 39 [58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_459 (a k) (relation_zero k) (e k 39)
lemma arrow_span_658 (b : Fin 75) : a k b*normalRep k 658 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_658_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 766)
  · rw [show a k b*normalRep k 658=0 from arrow_incompatible k b 39 3 [58, 34, 63, 21, 70, 22] (normal_endpoints 658) h]
    exact Submodule.zero_mem _
lemma extension_659_63 : a k 63*normalRep k 659=normalRep k 768 := by
  exact (walk_snoc k 40 [60, 4, 54, 15, 1, 34] 63).symm
lemma extension_659_64 : a k 64*normalRep k 659=0 := by
  change a k 64*walk k 40 [60, 4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_424 (a k) (relation_zero k) (e k 40)
lemma extension_659_65 : a k 65*normalRep k 659=0 := by
  change a k 65*walk k 40 [60, 4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_437 (a k) (relation_zero k) (e k 40)
lemma arrow_span_659 (b : Fin 75) : a k b*normalRep k 659 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_659_63 k]
      exact normal_mem k 768
    · rw [extension_659_64 k]
      exact Submodule.zero_mem _
    · rw [extension_659_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 659=0 from arrow_incompatible k b 40 41 [60, 4, 54, 15, 1, 34] (normal_endpoints 659) h]
    exact Submodule.zero_mem _
lemma extension_660_13 : a k 13*normalRep k 660=normalRep k 769 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33] 13).symm
lemma arrow_span_660 (b : Fin 75) : a k b*normalRep k 660 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_660_13 k]
      exact normal_mem k 769
  · rw [show a k b*normalRep k 660=0 from arrow_incompatible k b 40 13 [61, 35, 55, 27, 58, 33] (normal_endpoints 660) h]
    exact Submodule.zero_mem _
lemma extension_661_63 : a k 63*normalRep k 661=normalRep k 770 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 34] 63).symm
lemma extension_661_64 : a k 64*normalRep k 661=normalRep k 771 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 34] 64).symm
lemma extension_661_65 : a k 65*normalRep k 661=normalRep k 769 := by
  change a k 65*walk k 40 [61, 35, 55, 27, 58, 34]=walk k 40 [61, 35, 55, 27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_471 (a k) (relation_zero k) (e k 40)
lemma arrow_span_661 (b : Fin 75) : a k b*normalRep k 661 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_661_63 k]
      exact normal_mem k 770
    · rw [extension_661_64 k]
      exact normal_mem k 771
    · rw [extension_661_65 k]
      exact normal_mem k 769
  · rw [show a k b*normalRep k 661=0 from arrow_incompatible k b 40 41 [61, 35, 55, 27, 58, 34] (normal_endpoints 661) h]
    exact Submodule.zero_mem _
lemma extension_662_17 : a k 17*normalRep k 662=normalRep k 770 := by
  change a k 17*walk k 40 [61, 35, 55, 27, 59, 50]=walk k 40 [61, 35, 55, 27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_486 (a k) (relation_zero k) (e k 40)
lemma arrow_span_662 (b : Fin 75) : a k b*normalRep k 662 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_662_17 k]
      exact normal_mem k 770
  · rw [show a k b*normalRep k 662=0 from arrow_incompatible k b 40 16 [61, 35, 55, 27, 59, 50] (normal_endpoints 662) h]
    exact Submodule.zero_mem _
lemma extension_663_18 : a k 18*normalRep k 663=normalRep k 772 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24] 18).symm
lemma extension_663_19 : a k 19*normalRep k 663=normalRep k 773 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24] 19).symm
lemma arrow_span_663 (b : Fin 75) : a k b*normalRep k 663 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_663_18 k]
      exact normal_mem k 772
    · rw [extension_663_19 k]
      exact normal_mem k 773
  · rw [show a k b*normalRep k 663=0 from arrow_incompatible k b 41 17 [63, 21, 69, 8, 66, 24] (normal_endpoints 663) h]
    exact Submodule.zero_mem _
lemma extension_664_60 : a k 60*normalRep k 664=normalRep k 774 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 25] 60).symm
lemma extension_664_61 : a k 61*normalRep k 664=0 := by
  change a k 61*walk k 41 [63, 21, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_462 (a k) (relation_zero k) (e k 41)
lemma extension_664_62 : a k 62*normalRep k 664=normalRep k 773 := by
  change a k 62*walk k 41 [63, 21, 69, 8, 66, 25]=walk k 41 [63, 21, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_465 (a k) (relation_zero k) (e k 41)
lemma arrow_span_664 (b : Fin 75) : a k b*normalRep k 664 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_664_60 k]
      exact normal_mem k 774
    · rw [extension_664_61 k]
      exact Submodule.zero_mem _
    · rw [extension_664_62 k]
      exact normal_mem k 773
  · rw [show a k b*normalRep k 664=0 from arrow_incompatible k b 41 40 [63, 21, 69, 8, 66, 25] (normal_endpoints 664) h]
    exact Submodule.zero_mem _
lemma extension_665_14 : a k 14*normalRep k 665=(-normalRep k 772) := by
  change a k 14*walk k 41 [64, 36, 71, 72, 38, 28]=(-walk k 41 [63, 21, 69, 8, 66, 24, 18])
  rw [← walk_snoc]
  exact Universal.mul_reduced_468 (a k) (relation_zero k) (e k 41)
lemma arrow_span_665 (b : Fin 75) : a k b*normalRep k 665 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_665_14 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 772)
  · rw [show a k b*normalRep k 665=0 from arrow_incompatible k b 41 14 [64, 36, 71, 72, 38, 28] (normal_endpoints 665) h]
    exact Submodule.zero_mem _
lemma extension_666_57 : a k 57*normalRep k 666=normalRep k 775 := by
  exact (walk_snoc k 42 [66, 24, 18, 9, 41, 44] 57).symm
lemma extension_666_58 : a k 58*normalRep k 666=normalRep k 776 := by
  exact (walk_snoc k 42 [66, 24, 18, 9, 41, 44] 58).symm
lemma extension_666_59 : a k 59*normalRep k 666=0 := by
  change a k 59*walk k 42 [66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_447 (a k) (relation_zero k) (e k 42)
lemma arrow_span_666 (b : Fin 75) : a k b*normalRep k 666 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_666_57 k]
      exact normal_mem k 775
    · rw [extension_666_58 k]
      exact normal_mem k 776
    · rw [extension_666_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 666=0 from arrow_incompatible k b 42 39 [66, 24, 18, 9, 41, 44] (normal_endpoints 666) h]
    exact Submodule.zero_mem _
lemma extension_667_1 : a k 1*normalRep k 667=normalRep k 776 := by
  change a k 1*walk k 42 [66, 24, 19, 53, 54, 15]=walk k 42 [66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_444 (a k) (relation_zero k) (e k 42)
lemma arrow_span_667 (b : Fin 75) : a k b*normalRep k 667 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_667_1 k]
      exact normal_mem k 776
  · rw [show a k b*normalRep k 667=0 from arrow_incompatible k b 42 1 [66, 24, 19, 53, 54, 15] (normal_endpoints 667) h]
    exact Submodule.zero_mem _
lemma extension_668_57 : a k 57*normalRep k 668=0 := by
  change a k 57*walk k 42 [67, 32, 61, 35, 55, 27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_466 (a k) (relation_zero k) (e k 42)
lemma extension_668_58 : a k 58*normalRep k 668=normalRep k 777 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27] 58).symm
lemma extension_668_59 : a k 59*normalRep k 668=normalRep k 778 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27] 59).symm
lemma arrow_span_668 (b : Fin 75) : a k b*normalRep k 668 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_668_57 k]
      exact Submodule.zero_mem _
    · rw [extension_668_58 k]
      exact normal_mem k 777
    · rw [extension_668_59 k]
      exact normal_mem k 778
  · rw [show a k b*normalRep k 668=0 from arrow_incompatible k b 42 39 [67, 32, 61, 35, 55, 27] (normal_endpoints 668) h]
    exact Submodule.zero_mem _
lemma extension_669_47 : a k 47*normalRep k 669=normalRep k 779 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 56, 43] 47).symm
lemma extension_669_48 : a k 48*normalRep k 669=normalRep k 778 := by
  change a k 48*walk k 42 [67, 32, 61, 35, 56, 43]=walk k 42 [67, 32, 61, 35, 55, 27, 59]
  rw [← walk_snoc]
  exact Universal.mul_reduced_479 (a k) (relation_zero k) (e k 42)
lemma arrow_span_669 (b : Fin 75) : a k b*normalRep k 669 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_669_47 k]
      exact normal_mem k 779
    · rw [extension_669_48 k]
      exact normal_mem k 778
  · rw [show a k b*normalRep k 669=0 from arrow_incompatible k b 42 34 [67, 32, 61, 35, 56, 43] (normal_endpoints 669) h]
    exact Submodule.zero_mem _
lemma extension_670_6 : a k 6*normalRep k 670=normalRep k 779 := by
  change a k 6*walk k 42 [67, 32, 62, 52, 42, 45]=walk k 42 [67, 32, 61, 35, 56, 43, 47]
  rw [← walk_snoc]
  exact Universal.mul_reduced_480 (a k) (relation_zero k) (e k 42)
lemma arrow_span_670 (b : Fin 75) : a k b*normalRep k 670 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_670_6 k]
      exact normal_mem k 779
  · rw [show a k b*normalRep k 670=0 from arrow_incompatible k b 42 6 [67, 32, 62, 52, 42, 45] (normal_endpoints 670) h]
    exact Submodule.zero_mem _
lemma extension_671_41 : a k 41*normalRep k 671=normalRep k 780 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 18, 9] 41).symm
lemma extension_671_42 : a k 42*normalRep k 671=0 := by
  change a k 42*walk k 43 [69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_441 (a k) (relation_zero k) (e k 43)
lemma arrow_span_671 (b : Fin 75) : a k b*normalRep k 671 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_671_41 k]
      exact normal_mem k 780
    · rw [extension_671_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 671=0 from arrow_incompatible k b 43 31 [69, 8, 66, 24, 18, 9] (normal_endpoints 671) h]
    exact Submodule.zero_mem _
lemma extension_672_54 : a k 54*normalRep k 672=normalRep k 781 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 19, 53] 54).symm
lemma extension_672_55 : a k 55*normalRep k 672=0 := by
  change a k 55*walk k 43 [69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_429 (a k) (relation_zero k) (e k 43)
lemma extension_672_56 : a k 56*normalRep k 672=normalRep k 780 := by
  change a k 56*walk k 43 [69, 8, 66, 24, 19, 53]=walk k 43 [69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_488 (a k) (relation_zero k) (e k 43)
lemma arrow_span_672 (b : Fin 75) : a k b*normalRep k 672 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_672_54 k]
      exact normal_mem k 781
    · rw [extension_672_55 k]
      exact Submodule.zero_mem _
    · rw [extension_672_56 k]
      exact normal_mem k 780
  · rw [show a k b*normalRep k 672=0 from arrow_incompatible k b 43 38 [69, 8, 66, 24, 19, 53] (normal_endpoints 672) h]
    exact Submodule.zero_mem _
lemma extension_673_54 : a k 54*normalRep k 673=normalRep k 782 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 60, 4] 54).symm
lemma extension_673_55 : a k 55*normalRep k 673=0 := by
  change a k 55*walk k 43 [70, 22, 3, 40, 60, 4]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_430 (a k) (relation_zero k) (e k 43)
lemma extension_673_56 : a k 56*normalRep k 673=normalRep k 783 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 60, 4] 56).symm
lemma arrow_span_673 (b : Fin 75) : a k b*normalRep k 673 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_673_54 k]
      exact normal_mem k 782
    · rw [extension_673_55 k]
      exact Submodule.zero_mem _
    · rw [extension_673_56 k]
      exact normal_mem k 783
  · rw [show a k b*normalRep k 673=0 from arrow_incompatible k b 43 38 [70, 22, 3, 40, 60, 4] (normal_endpoints 673) h]
    exact Submodule.zero_mem _
lemma extension_674_41 : a k 41*normalRep k 674=normalRep k 783 := by
  change a k 41*walk k 43 [70, 22, 3, 40, 62, 52]=walk k 43 [70, 22, 3, 40, 60, 4, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_489 (a k) (relation_zero k) (e k 43)
lemma extension_674_42 : a k 42*normalRep k 674=0 := by
  change a k 42*walk k 43 [70, 22, 3, 40, 62, 52]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_428 (a k) (relation_zero k) (e k 43)
lemma arrow_span_674 (b : Fin 75) : a k b*normalRep k 674 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_674_41 k]
      exact normal_mem k 783
    · rw [extension_674_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 674=0 from arrow_incompatible k b 43 31 [70, 22, 3, 40, 62, 52] (normal_endpoints 674) h]
    exact Submodule.zero_mem _
lemma extension_675_43 : a k 43*normalRep k 675=0 := by
  change a k 43*walk k 44 [72, 37, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_433 (a k) (relation_zero k) (e k 44)
lemma extension_675_44 : a k 44*normalRep k 675=normalRep k 784 := by
  exact (walk_snoc k 44 [72, 37, 24, 18, 9, 41] 44).symm
lemma arrow_span_675 (b : Fin 75) : a k b*normalRep k 675 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_675_43 k]
      exact Submodule.zero_mem _
    · rw [extension_675_44 k]
      exact normal_mem k 784
  · rw [show a k b*normalRep k 675=0 from arrow_incompatible k b 44 32 [72, 37, 24, 18, 9, 41] (normal_endpoints 675) h]
    exact Submodule.zero_mem _
lemma extension_676_15 : a k 15*normalRep k 676=normalRep k 785 := by
  exact (walk_snoc k 44 [72, 37, 24, 19, 53, 54] 15).symm
lemma extension_676_16 : a k 16*normalRep k 676=normalRep k 784 := by
  change a k 16*walk k 44 [72, 37, 24, 19, 53, 54]=walk k 44 [72, 37, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_492 (a k) (relation_zero k) (e k 44)
lemma arrow_span_676 (b : Fin 75) : a k b*normalRep k 676 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_676_15 k]
      exact normal_mem k 785
    · rw [extension_676_16 k]
      exact normal_mem k 784
  · rw [show a k b*normalRep k 676=0 from arrow_incompatible k b 44 15 [72, 37, 24, 19, 53, 54] (normal_endpoints 676) h]
    exact Submodule.zero_mem _
lemma extension_677_27 : a k 27*normalRep k 677=normalRep k 786 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55] 27).symm
lemma arrow_span_677 (b : Fin 75) : a k b*normalRep k 677 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_677_27 k]
      exact normal_mem k 786
  · rw [show a k b*normalRep k 677=0 from arrow_incompatible k b 44 22 [73, 67, 32, 61, 35, 55] (normal_endpoints 677) h]
    exact Submodule.zero_mem _
lemma extension_678_43 : a k 43*normalRep k 678=normalRep k 787 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 56] 43).symm
lemma extension_678_44 : a k 44*normalRep k 678=normalRep k 786 := by
  change a k 44*walk k 44 [73, 67, 32, 61, 35, 56]=walk k 44 [73, 67, 32, 61, 35, 55, 27]
  rw [← walk_snoc]
  exact Universal.mul_reduced_493 (a k) (relation_zero k) (e k 44)
lemma arrow_span_678 (b : Fin 75) : a k b*normalRep k 678 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_678_43 k]
      exact normal_mem k 787
    · rw [extension_678_44 k]
      exact normal_mem k 786
  · rw [show a k b*normalRep k 678=0 from arrow_incompatible k b 44 32 [73, 67, 32, 61, 35, 56] (normal_endpoints 678) h]
    exact Submodule.zero_mem _
lemma extension_679_45 : a k 45*normalRep k 679=normalRep k 788 := by
  exact (walk_snoc k 44 [73, 67, 32, 62, 52, 42] 45).symm
lemma extension_679_46 : a k 46*normalRep k 679=normalRep k 787 := by
  change a k 46*walk k 44 [73, 67, 32, 62, 52, 42]=walk k 44 [73, 67, 32, 61, 35, 56, 43]
  rw [← walk_snoc]
  exact Universal.mul_reduced_478 (a k) (relation_zero k) (e k 44)
lemma arrow_span_679 (b : Fin 75) : a k b*normalRep k 679 ∈ normalSpan k := by
  by_cases h : arrowSource b=33
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [45, 46] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_679_45 k]
      exact normal_mem k 788
    · rw [extension_679_46 k]
      exact normal_mem k 787
  · rw [show a k b*normalRep k 679=0 from arrow_incompatible k b 44 33 [73, 67, 32, 62, 52, 42] (normal_endpoints 679) h]
    exact Submodule.zero_mem _
lemma extension_680_66 : a k 66*normalRep k 680=0 := by
  change a k 66*walk k 45 [74, 10, 11, 26, 31, 73]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_520 (a k) (relation_zero k) (e k 45)
lemma extension_680_67 : a k 67*normalRep k 680=normalRep k 789 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73] 67).symm
lemma extension_680_68 : a k 68*normalRep k 680=normalRep k 790 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73] 68).symm
lemma arrow_span_680 (b : Fin 75) : a k b*normalRep k 680 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_680_66 k]
      exact Submodule.zero_mem _
    · rw [extension_680_67 k]
      exact normal_mem k 789
    · rw [extension_680_68 k]
      exact normal_mem k 790
  · rw [show a k b*normalRep k 680=0 from arrow_incompatible k b 45 42 [74, 10, 11, 26, 31, 73] (normal_endpoints 680) h]
    exact Submodule.zero_mem _
lemma arrow_span_681 (b : Fin 75) : a k b*normalRep k 681 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 681=0 from arrow_incompatible k b 1 46 [1, 34, 63, 20, 30, 2, 0] (normal_endpoints 681) h]
    exact Submodule.zero_mem _
lemma extension_682_33 : a k 33*normalRep k 682=0 := by
  change a k 33*walk k 3 [3, 40, 60, 4, 54, 15, 1]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_521 (a k) (relation_zero k) (e k 3)
lemma extension_682_34 : a k 34*normalRep k 682=normalRep k 791 := by
  exact (walk_snoc k 3 [3, 40, 60, 4, 54, 15, 1] 34).symm
lemma arrow_span_682 (b : Fin 75) : a k b*normalRep k 682 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_682_33 k]
      exact Submodule.zero_mem _
    · rw [extension_682_34 k]
      exact normal_mem k 791
  · rw [show a k b*normalRep k 682=0 from arrow_incompatible k b 3 26 [3, 40, 60, 4, 54, 15, 1] (normal_endpoints 682) h]
    exact Submodule.zero_mem _
lemma extension_683_5 : a k 5*normalRep k 683=normalRep k 791 := by
  change a k 5*walk k 3 [3, 40, 60, 4, 54, 16, 57]=walk k 3 [3, 40, 60, 4, 54, 15, 1, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_596 (a k) (relation_zero k) (e k 3)
lemma arrow_span_683 (b : Fin 75) : a k b*normalRep k 683 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_683_5 k]
      exact normal_mem k 791
  · rw [show a k b*normalRep k 683=0 from arrow_incompatible k b 3 5 [3, 40, 60, 4, 54, 16, 57] (normal_endpoints 683) h]
    exact Submodule.zero_mem _
lemma extension_684_30 : a k 30*normalRep k 684=normalRep k 792 := by
  exact (walk_snoc k 4 [4, 54, 15, 1, 34, 63, 20] 30).symm
lemma extension_684_31 : a k 31*normalRep k 684=0 := by
  change a k 31*walk k 4 [4, 54, 15, 1, 34, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_555 (a k) (relation_zero k) (e k 4)
lemma arrow_span_684 (b : Fin 75) : a k b*normalRep k 684 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_684_30 k]
      exact normal_mem k 792
    · rw [extension_684_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 684=0 from arrow_incompatible k b 4 24 [4, 54, 15, 1, 34, 63, 20] (normal_endpoints 684) h]
    exact Submodule.zero_mem _
lemma extension_685_24 : a k 24*normalRep k 685=normalRep k 793 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66] 24).symm
lemma extension_685_25 : a k 25*normalRep k 685=normalRep k 794 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66] 25).symm
lemma arrow_span_685 (b : Fin 75) : a k b*normalRep k 685 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_685_24 k]
      exact normal_mem k 793
    · rw [extension_685_25 k]
      exact normal_mem k 794
  · rw [show a k b*normalRep k 685=0 from arrow_incompatible k b 6 20 [6, 7, 17, 21, 69, 8, 66] (normal_endpoints 685) h]
    exact Submodule.zero_mem _
lemma extension_686_39 : a k 39*normalRep k 686=0 := by
  change a k 39*walk k 6 [6, 7, 17, 21, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_527 (a k) (relation_zero k) (e k 6)
lemma extension_686_40 : a k 40*normalRep k 686=(-normalRep k 794) := by
  change a k 40*walk k 6 [6, 7, 17, 21, 69, 8, 68]=(-walk k 6 [6, 7, 17, 21, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_609 (a k) (relation_zero k) (e k 6)
lemma arrow_span_686 (b : Fin 75) : a k b*normalRep k 686 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_686_39 k]
      exact Submodule.zero_mem _
    · rw [extension_686_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 794)
  · rw [show a k b*normalRep k 686=0 from arrow_incompatible k b 6 30 [6, 7, 17, 21, 69, 8, 68] (normal_endpoints 686) h]
    exact Submodule.zero_mem _
lemma extension_687_18 : a k 18*normalRep k 687=normalRep k 795 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24] 18).symm
lemma extension_687_19 : a k 19*normalRep k 687=normalRep k 796 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24] 19).symm
lemma arrow_span_687 (b : Fin 75) : a k b*normalRep k 687 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_687_18 k]
      exact normal_mem k 795
    · rw [extension_687_19 k]
      exact normal_mem k 796
  · rw [show a k b*normalRep k 687=0 from arrow_incompatible k b 7 17 [7, 17, 21, 69, 8, 66, 24] (normal_endpoints 687) h]
    exact Submodule.zero_mem _
lemma extension_688_60 : a k 60*normalRep k 688=normalRep k 797 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 25] 60).symm
lemma extension_688_61 : a k 61*normalRep k 688=0 := by
  change a k 61*walk k 7 [7, 17, 21, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_563 (a k) (relation_zero k) (e k 7)
lemma extension_688_62 : a k 62*normalRep k 688=normalRep k 796 := by
  change a k 62*walk k 7 [7, 17, 21, 69, 8, 66, 25]=walk k 7 [7, 17, 21, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_566 (a k) (relation_zero k) (e k 7)
lemma arrow_span_688 (b : Fin 75) : a k b*normalRep k 688 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_688_60 k]
      exact normal_mem k 797
    · rw [extension_688_61 k]
      exact Submodule.zero_mem _
    · rw [extension_688_62 k]
      exact normal_mem k 796
  · rw [show a k b*normalRep k 688=0 from arrow_incompatible k b 7 40 [7, 17, 21, 69, 8, 66, 25] (normal_endpoints 688) h]
    exact Submodule.zero_mem _
lemma extension_689_57 : a k 57*normalRep k 689=normalRep k 798 := by
  exact (walk_snoc k 8 [8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_689_58 : a k 58*normalRep k 689=normalRep k 799 := by
  exact (walk_snoc k 8 [8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_689_59 : a k 59*normalRep k 689=0 := by
  change a k 59*walk k 8 [8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_547 (a k) (relation_zero k) (e k 8)
lemma arrow_span_689 (b : Fin 75) : a k b*normalRep k 689 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_689_57 k]
      exact normal_mem k 798
    · rw [extension_689_58 k]
      exact normal_mem k 799
    · rw [extension_689_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 689=0 from arrow_incompatible k b 8 39 [8, 66, 24, 18, 9, 41, 44] (normal_endpoints 689) h]
    exact Submodule.zero_mem _
lemma extension_690_1 : a k 1*normalRep k 690=normalRep k 799 := by
  change a k 1*walk k 8 [8, 66, 24, 19, 53, 54, 15]=walk k 8 [8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_544 (a k) (relation_zero k) (e k 8)
lemma arrow_span_690 (b : Fin 75) : a k b*normalRep k 690 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_690_1 k]
      exact normal_mem k 799
  · rw [show a k b*normalRep k 690=0 from arrow_incompatible k b 8 1 [8, 66, 24, 19, 53, 54, 15] (normal_endpoints 690) h]
    exact Submodule.zero_mem _
lemma extension_691_30 : a k 30*normalRep k 691=normalRep k 800 := by
  exact (walk_snoc k 9 [9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_691_31 : a k 31*normalRep k 691=0 := by
  change a k 31*walk k 9 [9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_556 (a k) (relation_zero k) (e k 9)
lemma arrow_span_691 (b : Fin 75) : a k b*normalRep k 691 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_691_30 k]
      exact normal_mem k 800
    · rw [extension_691_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 691=0 from arrow_incompatible k b 9 24 [9, 41, 44, 57, 5, 63, 20] (normal_endpoints 691) h]
    exact Submodule.zero_mem _
lemma extension_692_60 : a k 60*normalRep k 692=0 := by
  change a k 60*walk k 10 [10, 11, 26, 31, 73, 67, 32]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_572 (a k) (relation_zero k) (e k 10)
lemma extension_692_61 : a k 61*normalRep k 692=normalRep k 801 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32] 61).symm
lemma extension_692_62 : a k 62*normalRep k 692=normalRep k 802 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32] 62).symm
lemma arrow_span_692 (b : Fin 75) : a k b*normalRep k 692 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_692_60 k]
      exact Submodule.zero_mem _
    · rw [extension_692_61 k]
      exact normal_mem k 801
    · rw [extension_692_62 k]
      exact normal_mem k 802
  · rw [show a k b*normalRep k 692=0 from arrow_incompatible k b 10 40 [10, 11, 26, 31, 73, 67, 32] (normal_endpoints 692) h]
    exact Submodule.zero_mem _
lemma extension_693_12 : a k 12*normalRep k 693=normalRep k 801 := by
  change a k 12*walk k 10 [10, 11, 26, 31, 73, 68, 39]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61]
  rw [← walk_snoc]
  exact Universal.mul_reduced_580 (a k) (relation_zero k) (e k 10)
lemma arrow_span_693 (b : Fin 75) : a k b*normalRep k 693 ∈ normalSpan k := by
  by_cases h : arrowSource b=12
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [12] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_693_12 k]
      exact normal_mem k 801
  · rw [show a k b*normalRep k 693=0 from arrow_incompatible k b 10 12 [10, 11, 26, 31, 73, 68, 39] (normal_endpoints 693) h]
    exact Submodule.zero_mem _
lemma extension_694_35 : a k 35*normalRep k 694=normalRep k 803 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61] 35).symm
lemma arrow_span_694 (b : Fin 75) : a k b*normalRep k 694 ∈ normalSpan k := by
  by_cases h : arrowSource b=27
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [35] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_694_35 k]
      exact normal_mem k 803
  · rw [show a k b*normalRep k 694=0 from arrow_incompatible k b 11 27 [11, 26, 31, 73, 67, 32, 61] (normal_endpoints 694) h]
    exact Submodule.zero_mem _
lemma extension_695_52 : a k 52*normalRep k 695=normalRep k 804 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 62] 52).symm
lemma extension_695_53 : a k 53*normalRep k 695=normalRep k 803 := by
  change a k 53*walk k 11 [11, 26, 31, 73, 67, 32, 62]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35]
  rw [← walk_snoc]
  exact Universal.mul_reduced_600 (a k) (relation_zero k) (e k 11)
lemma arrow_span_695 (b : Fin 75) : a k b*normalRep k 695 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_695_52 k]
      exact normal_mem k 804
    · rw [extension_695_53 k]
      exact normal_mem k 803
  · rw [show a k b*normalRep k 695=0 from arrow_incompatible k b 11 37 [11, 26, 31, 73, 67, 32, 62] (normal_endpoints 695) h]
    exact Submodule.zero_mem _
lemma extension_696_49 : a k 49*normalRep k 696=normalRep k 805 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13] 49).symm
lemma arrow_span_696 (b : Fin 75) : a k b*normalRep k 696 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_696_49 k]
      exact normal_mem k 805
  · rw [show a k b*normalRep k 696=0 from arrow_incompatible k b 12 35 [12, 35, 55, 27, 58, 33, 13] (normal_endpoints 696) h]
    exact Submodule.zero_mem _
lemma extension_697_20 : a k 20*normalRep k 697=0 := by
  change a k 20*walk k 12 [12, 35, 55, 27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_550 (a k) (relation_zero k) (e k 12)
lemma extension_697_21 : a k 21*normalRep k 697=normalRep k 806 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 34, 63] 21).symm
lemma arrow_span_697 (b : Fin 75) : a k b*normalRep k 697 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_697_20 k]
      exact Submodule.zero_mem _
    · rw [extension_697_21 k]
      exact normal_mem k 806
  · rw [show a k b*normalRep k 697=0 from arrow_incompatible k b 12 18 [12, 35, 55, 27, 58, 34, 63] (normal_endpoints 697) h]
    exact Submodule.zero_mem _
lemma extension_698_36 : a k 36*normalRep k 698=normalRep k 806 + normalRep k 805 := by
  change a k 36*walk k 12 [12, 35, 55, 27, 58, 34, 64]=walk k 12 [12, 35, 55, 27, 58, 34, 63, 21] + walk k 12 [12, 35, 55, 27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_604 (a k) (relation_zero k) (e k 12)
lemma arrow_span_698 (b : Fin 75) : a k b*normalRep k 698 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_698_36 k]
      exact (normalSpan k).add_mem (normal_mem k 806) (normal_mem k 805)
  · rw [show a k b*normalRep k 698=0 from arrow_incompatible k b 12 28 [12, 35, 55, 27, 58, 34, 64] (normal_endpoints 698) h]
    exact Submodule.zero_mem _
lemma extension_699_9 : a k 9*normalRep k 699=normalRep k 807 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_699 (b : Fin 75) : a k b*normalRep k 699 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_699_9 k]
      exact normal_mem k 807
  · rw [show a k b*normalRep k 699=0 from arrow_incompatible k b 13 9 [13, 49, 69, 8, 66, 24, 18] (normal_endpoints 699) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
