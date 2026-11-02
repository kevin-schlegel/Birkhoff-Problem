import N6NormalData
import N6Reduced8
import N6Reduced9
import N6Reduced10
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_700_52 : a k 52*normalRep k 700=normalRep k 807 := by
  change a k 52*walk k 13 [13, 49, 69, 8, 66, 24, 19]=walk k 13 [13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_552 (a k) (relation_zero k) (e k 13)
lemma extension_700_53 : a k 53*normalRep k 700=normalRep k 808 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_700 (b : Fin 75) : a k b*normalRep k 700 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_700_52 k]
      exact normal_mem k 807
    · rw [extension_700_53 k]
      exact normal_mem k 808
  · rw [show a k b*normalRep k 700=0 from arrow_incompatible k b 13 37 [13, 49, 69, 8, 66, 24, 19] (normal_endpoints 700) h]
    exact Submodule.zero_mem _
lemma extension_701_4 : a k 4*normalRep k 701=normalRep k 808 := by
  change a k 4*walk k 13 [13, 49, 69, 8, 66, 25, 60]=walk k 13 [13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_601 (a k) (relation_zero k) (e k 13)
lemma arrow_span_701 (b : Fin 75) : a k b*normalRep k 701 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_701_4 k]
      exact normal_mem k 808
  · rw [show a k b*normalRep k 701=0 from arrow_incompatible k b 13 4 [13, 49, 69, 8, 66, 25, 60] (normal_endpoints 701) h]
    exact Submodule.zero_mem _
lemma extension_702_20 : a k 20*normalRep k 702=normalRep k 809 := by
  exact (walk_snoc k 14 [14, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_702_21 : a k 21*normalRep k 702=0 := by
  change a k 21*walk k 14 [14, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_605 (a k) (relation_zero k) (e k 14)
lemma arrow_span_702 (b : Fin 75) : a k b*normalRep k 702 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_702_20 k]
      exact normal_mem k 809
    · rw [extension_702_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 702=0 from arrow_incompatible k b 14 18 [14, 9, 41, 44, 57, 5, 63] (normal_endpoints 702) h]
    exact Submodule.zero_mem _
lemma extension_703_0 : a k 0*normalRep k 703=normalRep k 810 := by
  exact (walk_snoc k 15 [15, 1, 34, 63, 20, 30, 2] 0).symm
lemma arrow_span_703 (b : Fin 75) : a k b*normalRep k 703 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_703_0 k]
      exact normal_mem k 810
  · rw [show a k b*normalRep k 703=0 from arrow_incompatible k b 15 0 [15, 1, 34, 63, 20, 30, 2] (normal_endpoints 703) h]
    exact Submodule.zero_mem _
lemma extension_704_9 : a k 9*normalRep k 704=normalRep k 811 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_704 (b : Fin 75) : a k b*normalRep k 704 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_704_9 k]
      exact normal_mem k 811
  · rw [show a k b*normalRep k 704=0 from arrow_incompatible k b 16 9 [17, 21, 69, 8, 66, 24, 18] (normal_endpoints 704) h]
    exact Submodule.zero_mem _
lemma extension_705_52 : a k 52*normalRep k 705=normalRep k 811 := by
  change a k 52*walk k 16 [17, 21, 69, 8, 66, 24, 19]=walk k 16 [17, 21, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_553 (a k) (relation_zero k) (e k 16)
lemma extension_705_53 : a k 53*normalRep k 705=normalRep k 812 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_705 (b : Fin 75) : a k b*normalRep k 705 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_705_52 k]
      exact normal_mem k 811
    · rw [extension_705_53 k]
      exact normal_mem k 812
  · rw [show a k b*normalRep k 705=0 from arrow_incompatible k b 16 37 [17, 21, 69, 8, 66, 24, 19] (normal_endpoints 705) h]
    exact Submodule.zero_mem _
lemma extension_706_4 : a k 4*normalRep k 706=normalRep k 812 := by
  change a k 4*walk k 16 [17, 21, 69, 8, 66, 25, 60]=walk k 16 [17, 21, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_602 (a k) (relation_zero k) (e k 16)
lemma arrow_span_706 (b : Fin 75) : a k b*normalRep k 706 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_706_4 k]
      exact normal_mem k 812
  · rw [show a k b*normalRep k 706=0 from arrow_incompatible k b 16 4 [17, 21, 69, 8, 66, 25, 60] (normal_endpoints 706) h]
    exact Submodule.zero_mem _
lemma extension_707_20 : a k 20*normalRep k 707=normalRep k 813 := by
  exact (walk_snoc k 17 [18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_707_21 : a k 21*normalRep k 707=0 := by
  change a k 21*walk k 17 [18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_606 (a k) (relation_zero k) (e k 17)
lemma arrow_span_707 (b : Fin 75) : a k b*normalRep k 707 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_707_20 k]
      exact normal_mem k 813
    · rw [extension_707_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 707=0 from arrow_incompatible k b 17 18 [18, 9, 41, 44, 57, 5, 63] (normal_endpoints 707) h]
    exact Submodule.zero_mem _
lemma extension_708_41 : a k 41*normalRep k 708=normalRep k 814 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_708_42 : a k 42*normalRep k 708=0 := by
  change a k 42*walk k 18 [21, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_530 (a k) (relation_zero k) (e k 18)
lemma arrow_span_708 (b : Fin 75) : a k b*normalRep k 708 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_708_41 k]
      exact normal_mem k 814
    · rw [extension_708_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 708=0 from arrow_incompatible k b 18 31 [21, 69, 8, 66, 24, 18, 9] (normal_endpoints 708) h]
    exact Submodule.zero_mem _
lemma extension_709_54 : a k 54*normalRep k 709=normalRep k 815 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_709_55 : a k 55*normalRep k 709=0 := by
  change a k 55*walk k 18 [21, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_532 (a k) (relation_zero k) (e k 18)
lemma extension_709_56 : a k 56*normalRep k 709=normalRep k 814 := by
  change a k 56*walk k 18 [21, 69, 8, 66, 24, 19, 53]=walk k 18 [21, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_589 (a k) (relation_zero k) (e k 18)
lemma arrow_span_709 (b : Fin 75) : a k b*normalRep k 709 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_709_54 k]
      exact normal_mem k 815
    · rw [extension_709_55 k]
      exact Submodule.zero_mem _
    · rw [extension_709_56 k]
      exact normal_mem k 814
  · rw [show a k b*normalRep k 709=0 from arrow_incompatible k b 18 38 [21, 69, 8, 66, 24, 19, 53] (normal_endpoints 709) h]
    exact Submodule.zero_mem _
lemma extension_710_1 : a k 1*normalRep k 710=normalRep k 816 := by
  exact (walk_snoc k 19 [22, 3, 40, 60, 4, 54, 15] 1).symm
lemma arrow_span_710 (b : Fin 75) : a k b*normalRep k 710 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_710_1 k]
      exact normal_mem k 816
  · rw [show a k b*normalRep k 710=0 from arrow_incompatible k b 19 1 [22, 3, 40, 60, 4, 54, 15] (normal_endpoints 710) h]
    exact Submodule.zero_mem _
lemma extension_711_57 : a k 57*normalRep k 711=normalRep k 817 := by
  exact (walk_snoc k 19 [22, 3, 40, 60, 4, 54, 16] 57).symm
lemma extension_711_58 : a k 58*normalRep k 711=normalRep k 816 := by
  change a k 58*walk k 19 [22, 3, 40, 60, 4, 54, 16]=walk k 19 [22, 3, 40, 60, 4, 54, 15, 1]
  rw [← walk_snoc]
  exact Universal.mul_reduced_545 (a k) (relation_zero k) (e k 19)
lemma extension_711_59 : a k 59*normalRep k 711=0 := by
  change a k 59*walk k 19 [22, 3, 40, 60, 4, 54, 16]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_548 (a k) (relation_zero k) (e k 19)
lemma arrow_span_711 (b : Fin 75) : a k b*normalRep k 711 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_711_57 k]
      exact normal_mem k 817
    · rw [extension_711_58 k]
      exact normal_mem k 816
    · rw [extension_711_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 711=0 from arrow_incompatible k b 19 39 [22, 3, 40, 60, 4, 54, 16] (normal_endpoints 711) h]
    exact Submodule.zero_mem _
lemma extension_712_63 : a k 63*normalRep k 712=normalRep k 818 := by
  exact (walk_snoc k 20 [24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_712_64 : a k 64*normalRep k 712=0 := by
  change a k 64*walk k 20 [24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_524 (a k) (relation_zero k) (e k 20)
lemma extension_712_65 : a k 65*normalRep k 712=0 := by
  change a k 65*walk k 20 [24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_537 (a k) (relation_zero k) (e k 20)
lemma arrow_span_712 (b : Fin 75) : a k b*normalRep k 712 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_712_63 k]
      exact normal_mem k 818
    · rw [extension_712_64 k]
      exact Submodule.zero_mem _
    · rw [extension_712_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 712=0 from arrow_incompatible k b 20 41 [24, 18, 9, 41, 44, 57, 5] (normal_endpoints 712) h]
    exact Submodule.zero_mem _
lemma extension_713_54 : a k 54*normalRep k 713=0 := by
  change a k 54*walk k 21 [26, 31, 73, 67, 32, 61, 35]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_575 (a k) (relation_zero k) (e k 21)
lemma extension_713_55 : a k 55*normalRep k 713=normalRep k 819 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35] 55).symm
lemma extension_713_56 : a k 56*normalRep k 713=normalRep k 820 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35] 56).symm
lemma arrow_span_713 (b : Fin 75) : a k b*normalRep k 713 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_713_54 k]
      exact Submodule.zero_mem _
    · rw [extension_713_55 k]
      exact normal_mem k 819
    · rw [extension_713_56 k]
      exact normal_mem k 820
  · rw [show a k b*normalRep k 713=0 from arrow_incompatible k b 21 38 [26, 31, 73, 67, 32, 61, 35] (normal_endpoints 713) h]
    exact Submodule.zero_mem _
lemma extension_714_41 : a k 41*normalRep k 714=normalRep k 820 := by
  change a k 41*walk k 21 [26, 31, 73, 67, 32, 62, 52]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_590 (a k) (relation_zero k) (e k 21)
lemma extension_714_42 : a k 42*normalRep k 714=normalRep k 821 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 62, 52] 42).symm
lemma arrow_span_714 (b : Fin 75) : a k b*normalRep k 714 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_714_41 k]
      exact normal_mem k 820
    · rw [extension_714_42 k]
      exact normal_mem k 821
  · rw [show a k b*normalRep k 714=0 from arrow_incompatible k b 21 31 [26, 31, 73, 67, 32, 62, 52] (normal_endpoints 714) h]
    exact Submodule.zero_mem _
lemma extension_715_66 : a k 66*normalRep k 715=normalRep k 822 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_715_67 : a k 67*normalRep k 715=0 := by
  change a k 67*walk k 22 [27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_540 (a k) (relation_zero k) (e k 22)
lemma extension_715_68 : a k 68*normalRep k 715=normalRep k 823 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_715 (b : Fin 75) : a k b*normalRep k 715 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_715_66 k]
      exact normal_mem k 822
    · rw [extension_715_67 k]
      exact Submodule.zero_mem _
    · rw [extension_715_68 k]
      exact normal_mem k 823
  · rw [show a k b*normalRep k 715=0 from arrow_incompatible k b 22 42 [27, 58, 33, 13, 49, 69, 8] (normal_endpoints 715) h]
    exact Submodule.zero_mem _
lemma extension_716_37 : a k 37*normalRep k 716=normalRep k 822 := by
  change a k 37*walk k 22 [27, 58, 33, 13, 49, 71, 72]=walk k 22 [27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_617 (a k) (relation_zero k) (e k 22)
lemma extension_716_38 : a k 38*normalRep k 716=normalRep k 824 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_716 (b : Fin 75) : a k b*normalRep k 716 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_716_37 k]
      exact normal_mem k 822
    · rw [extension_716_38 k]
      exact normal_mem k 824
  · rw [show a k b*normalRep k 716=0 from arrow_incompatible k b 22 29 [27, 58, 33, 13, 49, 71, 72] (normal_endpoints 716) h]
    exact Submodule.zero_mem _
lemma extension_717_3 : a k 3*normalRep k 717=(-normalRep k 823) := by
  change a k 3*walk k 22 [27, 58, 34, 63, 21, 70, 22]=(-walk k 22 [27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_560 (a k) (relation_zero k) (e k 22)
lemma arrow_span_717 (b : Fin 75) : a k b*normalRep k 717 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_717_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 823)
  · rw [show a k b*normalRep k 717=0 from arrow_incompatible k b 22 3 [27, 58, 34, 63, 21, 70, 22] (normal_endpoints 717) h]
    exact Submodule.zero_mem _
lemma extension_718_63 : a k 63*normalRep k 718=normalRep k 825 := by
  exact (walk_snoc k 23 [28, 14, 9, 41, 44, 57, 5] 63).symm
lemma extension_718_64 : a k 64*normalRep k 718=0 := by
  change a k 64*walk k 23 [28, 14, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_525 (a k) (relation_zero k) (e k 23)
lemma extension_718_65 : a k 65*normalRep k 718=0 := by
  change a k 65*walk k 23 [28, 14, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_538 (a k) (relation_zero k) (e k 23)
lemma arrow_span_718 (b : Fin 75) : a k b*normalRep k 718 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_718_63 k]
      exact normal_mem k 825
    · rw [extension_718_64 k]
      exact Submodule.zero_mem _
    · rw [extension_718_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 718=0 from arrow_incompatible k b 23 41 [28, 14, 9, 41, 44, 57, 5] (normal_endpoints 718) h]
    exact Submodule.zero_mem _
lemma extension_719_27 : a k 27*normalRep k 719=normalRep k 826 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55] 27).symm
lemma arrow_span_719 (b : Fin 75) : a k b*normalRep k 719 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_719_27 k]
      exact normal_mem k 826
  · rw [show a k b*normalRep k 719=0 from arrow_incompatible k b 24 22 [31, 73, 67, 32, 61, 35, 55] (normal_endpoints 719) h]
    exact Submodule.zero_mem _
lemma extension_720_43 : a k 43*normalRep k 720=normalRep k 827 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 56] 43).symm
lemma extension_720_44 : a k 44*normalRep k 720=normalRep k 826 := by
  change a k 44*walk k 24 [31, 73, 67, 32, 61, 35, 56]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27]
  rw [← walk_snoc]
  exact Universal.mul_reduced_593 (a k) (relation_zero k) (e k 24)
lemma arrow_span_720 (b : Fin 75) : a k b*normalRep k 720 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_720_43 k]
      exact normal_mem k 827
    · rw [extension_720_44 k]
      exact normal_mem k 826
  · rw [show a k b*normalRep k 720=0 from arrow_incompatible k b 24 32 [31, 73, 67, 32, 61, 35, 56] (normal_endpoints 720) h]
    exact Submodule.zero_mem _
lemma extension_721_45 : a k 45*normalRep k 721=normalRep k 828 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 62, 52, 42] 45).symm
lemma extension_721_46 : a k 46*normalRep k 721=normalRep k 827 := by
  change a k 46*walk k 24 [31, 73, 67, 32, 62, 52, 42]=walk k 24 [31, 73, 67, 32, 61, 35, 56, 43]
  rw [← walk_snoc]
  exact Universal.mul_reduced_581 (a k) (relation_zero k) (e k 24)
lemma arrow_span_721 (b : Fin 75) : a k b*normalRep k 721 ∈ normalSpan k := by
  by_cases h : arrowSource b=33
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [45, 46] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_721_45 k]
      exact normal_mem k 828
    · rw [extension_721_46 k]
      exact normal_mem k 827
  · rw [show a k b*normalRep k 721=0 from arrow_incompatible k b 24 33 [31, 73, 67, 32, 62, 52, 42] (normal_endpoints 721) h]
    exact Submodule.zero_mem _
lemma extension_722_13 : a k 13*normalRep k 722=normalRep k 829 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33] 13).symm
lemma arrow_span_722 (b : Fin 75) : a k b*normalRep k 722 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_722_13 k]
      exact normal_mem k 829
  · rw [show a k b*normalRep k 722=0 from arrow_incompatible k b 25 13 [32, 61, 35, 55, 27, 58, 33] (normal_endpoints 722) h]
    exact Submodule.zero_mem _
lemma extension_723_63 : a k 63*normalRep k 723=normalRep k 830 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 34] 63).symm
lemma extension_723_64 : a k 64*normalRep k 723=normalRep k 831 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 34] 64).symm
lemma extension_723_65 : a k 65*normalRep k 723=normalRep k 829 := by
  change a k 65*walk k 25 [32, 61, 35, 55, 27, 58, 34]=walk k 25 [32, 61, 35, 55, 27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_573 (a k) (relation_zero k) (e k 25)
lemma arrow_span_723 (b : Fin 75) : a k b*normalRep k 723 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_723_63 k]
      exact normal_mem k 830
    · rw [extension_723_64 k]
      exact normal_mem k 831
    · rw [extension_723_65 k]
      exact normal_mem k 829
  · rw [show a k b*normalRep k 723=0 from arrow_incompatible k b 25 41 [32, 61, 35, 55, 27, 58, 34] (normal_endpoints 723) h]
    exact Submodule.zero_mem _
lemma extension_724_17 : a k 17*normalRep k 724=normalRep k 830 := by
  change a k 17*walk k 25 [32, 61, 35, 55, 27, 59, 50]=walk k 25 [32, 61, 35, 55, 27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_587 (a k) (relation_zero k) (e k 25)
lemma arrow_span_724 (b : Fin 75) : a k b*normalRep k 724 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_724_17 k]
      exact normal_mem k 830
  · rw [show a k b*normalRep k 724=0 from arrow_incompatible k b 25 16 [32, 61, 35, 55, 27, 59, 50] (normal_endpoints 724) h]
    exact Submodule.zero_mem _
lemma extension_725_18 : a k 18*normalRep k 725=normalRep k 832 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_725_19 : a k 19*normalRep k 725=normalRep k 833 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_725 (b : Fin 75) : a k b*normalRep k 725 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_725_18 k]
      exact normal_mem k 832
    · rw [extension_725_19 k]
      exact normal_mem k 833
  · rw [show a k b*normalRep k 725=0 from arrow_incompatible k b 26 17 [33, 13, 49, 69, 8, 66, 24] (normal_endpoints 725) h]
    exact Submodule.zero_mem _
lemma extension_726_60 : a k 60*normalRep k 726=normalRep k 834 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_726_61 : a k 61*normalRep k 726=0 := by
  change a k 61*walk k 26 [33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_564 (a k) (relation_zero k) (e k 26)
lemma extension_726_62 : a k 62*normalRep k 726=normalRep k 833 := by
  change a k 62*walk k 26 [33, 13, 49, 69, 8, 66, 25]=walk k 26 [33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_567 (a k) (relation_zero k) (e k 26)
lemma arrow_span_726 (b : Fin 75) : a k b*normalRep k 726 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_726_60 k]
      exact normal_mem k 834
    · rw [extension_726_61 k]
      exact Submodule.zero_mem _
    · rw [extension_726_62 k]
      exact normal_mem k 833
  · rw [show a k b*normalRep k 726=0 from arrow_incompatible k b 26 40 [33, 13, 49, 69, 8, 66, 25] (normal_endpoints 726) h]
    exact Submodule.zero_mem _
lemma extension_727_14 : a k 14*normalRep k 727=normalRep k 832 := by
  change a k 14*walk k 26 [33, 13, 49, 71, 72, 38, 28]=walk k 26 [33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_570 (a k) (relation_zero k) (e k 26)
lemma arrow_span_727 (b : Fin 75) : a k b*normalRep k 727 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_727_14 k]
      exact normal_mem k 832
  · rw [show a k b*normalRep k 727=0 from arrow_incompatible k b 26 14 [33, 13, 49, 71, 72, 38, 28] (normal_endpoints 727) h]
    exact Submodule.zero_mem _
lemma extension_728_69 : a k 69*normalRep k 728=normalRep k 835 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49] 69).symm
lemma extension_728_70 : a k 70*normalRep k 728=0 := by
  change a k 70*walk k 27 [35, 55, 27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_585 (a k) (relation_zero k) (e k 27)
lemma extension_728_71 : a k 71*normalRep k 728=normalRep k 836 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49] 71).symm
lemma arrow_span_728 (b : Fin 75) : a k b*normalRep k 728 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_728_69 k]
      exact normal_mem k 835
    · rw [extension_728_70 k]
      exact Submodule.zero_mem _
    · rw [extension_728_71 k]
      exact normal_mem k 836
  · rw [show a k b*normalRep k 728=0 from arrow_incompatible k b 27 43 [35, 55, 27, 58, 33, 13, 49] (normal_endpoints 728) h]
    exact Submodule.zero_mem _
lemma extension_729_69 : a k 69*normalRep k 729=(-normalRep k 835) := by
  change a k 69*walk k 27 [35, 55, 27, 58, 34, 63, 21]=(-walk k 27 [35, 55, 27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_576 (a k) (relation_zero k) (e k 27)
lemma extension_729_70 : a k 70*normalRep k 729=normalRep k 837 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 34, 63, 21] 70).symm
lemma extension_729_71 : a k 71*normalRep k 729=0 := by
  change a k 71*walk k 27 [35, 55, 27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_558 (a k) (relation_zero k) (e k 27)
lemma arrow_span_729 (b : Fin 75) : a k b*normalRep k 729 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_729_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 835)
    · rw [extension_729_70 k]
      exact normal_mem k 837
    · rw [extension_729_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 729=0 from arrow_incompatible k b 27 43 [35, 55, 27, 58, 34, 63, 21] (normal_endpoints 729) h]
    exact Submodule.zero_mem _
lemma extension_730_54 : a k 54*normalRep k 730=normalRep k 838 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 60, 4] 54).symm
lemma extension_730_55 : a k 55*normalRep k 730=0 := by
  change a k 55*walk k 28 [36, 70, 22, 3, 40, 60, 4]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_533 (a k) (relation_zero k) (e k 28)
lemma extension_730_56 : a k 56*normalRep k 730=normalRep k 839 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 60, 4] 56).symm
lemma arrow_span_730 (b : Fin 75) : a k b*normalRep k 730 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_730_54 k]
      exact normal_mem k 838
    · rw [extension_730_55 k]
      exact Submodule.zero_mem _
    · rw [extension_730_56 k]
      exact normal_mem k 839
  · rw [show a k b*normalRep k 730=0 from arrow_incompatible k b 28 38 [36, 70, 22, 3, 40, 60, 4] (normal_endpoints 730) h]
    exact Submodule.zero_mem _
lemma extension_731_41 : a k 41*normalRep k 731=normalRep k 839 := by
  change a k 41*walk k 28 [36, 70, 22, 3, 40, 62, 52]=walk k 28 [36, 70, 22, 3, 40, 60, 4, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_591 (a k) (relation_zero k) (e k 28)
lemma extension_731_42 : a k 42*normalRep k 731=0 := by
  change a k 42*walk k 28 [36, 70, 22, 3, 40, 62, 52]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_531 (a k) (relation_zero k) (e k 28)
lemma arrow_span_731 (b : Fin 75) : a k b*normalRep k 731 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_731_41 k]
      exact normal_mem k 839
    · rw [extension_731_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 731=0 from arrow_incompatible k b 28 31 [36, 70, 22, 3, 40, 62, 52] (normal_endpoints 731) h]
    exact Submodule.zero_mem _
lemma extension_732_5 : a k 5*normalRep k 732=normalRep k 840 := by
  exact (walk_snoc k 29 [37, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_732 (b : Fin 75) : a k b*normalRep k 732 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_732_5 k]
      exact normal_mem k 840
  · rw [show a k b*normalRep k 732=0 from arrow_incompatible k b 29 5 [37, 24, 18, 9, 41, 44, 57] (normal_endpoints 732) h]
    exact Submodule.zero_mem _
lemma extension_733_33 : a k 33*normalRep k 733=0 := by
  change a k 33*walk k 29 [37, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_522 (a k) (relation_zero k) (e k 29)
lemma extension_733_34 : a k 34*normalRep k 733=normalRep k 840 := by
  change a k 34*walk k 29 [37, 24, 18, 9, 41, 44, 58]=walk k 29 [37, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_597 (a k) (relation_zero k) (e k 29)
lemma arrow_span_733 (b : Fin 75) : a k b*normalRep k 733 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_733_33 k]
      exact Submodule.zero_mem _
    · rw [extension_733_34 k]
      exact normal_mem k 840
  · rw [show a k b*normalRep k 733=0 from arrow_incompatible k b 29 26 [37, 24, 18, 9, 41, 44, 58] (normal_endpoints 733) h]
    exact Submodule.zero_mem _
lemma extension_734_13 : a k 13*normalRep k 734=normalRep k 841 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33] 13).symm
lemma arrow_span_734 (b : Fin 75) : a k b*normalRep k 734 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_734_13 k]
      exact normal_mem k 841
  · rw [show a k b*normalRep k 734=0 from arrow_incompatible k b 30 13 [39, 12, 35, 55, 27, 58, 33] (normal_endpoints 734) h]
    exact Submodule.zero_mem _
lemma extension_735_63 : a k 63*normalRep k 735=normalRep k 842 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 34] 63).symm
lemma extension_735_64 : a k 64*normalRep k 735=normalRep k 843 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 34] 64).symm
lemma extension_735_65 : a k 65*normalRep k 735=normalRep k 841 := by
  change a k 65*walk k 30 [39, 12, 35, 55, 27, 58, 34]=walk k 30 [39, 12, 35, 55, 27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_574 (a k) (relation_zero k) (e k 30)
lemma arrow_span_735 (b : Fin 75) : a k b*normalRep k 735 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_735_63 k]
      exact normal_mem k 842
    · rw [extension_735_64 k]
      exact normal_mem k 843
    · rw [extension_735_65 k]
      exact normal_mem k 841
  · rw [show a k b*normalRep k 735=0 from arrow_incompatible k b 30 41 [39, 12, 35, 55, 27, 58, 34] (normal_endpoints 735) h]
    exact Submodule.zero_mem _
lemma extension_736_17 : a k 17*normalRep k 736=normalRep k 842 := by
  change a k 17*walk k 30 [39, 12, 35, 55, 27, 59, 50]=walk k 30 [39, 12, 35, 55, 27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_588 (a k) (relation_zero k) (e k 30)
lemma arrow_span_736 (b : Fin 75) : a k b*normalRep k 736 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_736_17 k]
      exact normal_mem k 842
  · rw [show a k b*normalRep k 736=0 from arrow_incompatible k b 30 16 [39, 12, 35, 55, 27, 59, 50] (normal_endpoints 736) h]
    exact Submodule.zero_mem _
lemma extension_737_63 : a k 63*normalRep k 737=normalRep k 844 := by
  exact (walk_snoc k 30 [40, 60, 4, 54, 15, 1, 34] 63).symm
lemma extension_737_64 : a k 64*normalRep k 737=0 := by
  change a k 64*walk k 30 [40, 60, 4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_526 (a k) (relation_zero k) (e k 30)
lemma extension_737_65 : a k 65*normalRep k 737=0 := by
  change a k 65*walk k 30 [40, 60, 4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_539 (a k) (relation_zero k) (e k 30)
lemma arrow_span_737 (b : Fin 75) : a k b*normalRep k 737 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_737_63 k]
      exact normal_mem k 844
    · rw [extension_737_64 k]
      exact Submodule.zero_mem _
    · rw [extension_737_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 737=0 from arrow_incompatible k b 30 41 [40, 60, 4, 54, 15, 1, 34] (normal_endpoints 737) h]
    exact Submodule.zero_mem _
lemma extension_738_8 : a k 8*normalRep k 738=normalRep k 845 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69] 8).symm
lemma arrow_span_738 (b : Fin 75) : a k b*normalRep k 738 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_738_8 k]
      exact normal_mem k 845
  · rw [show a k b*normalRep k 738=0 from arrow_incompatible k b 31 8 [41, 43, 47, 7, 17, 21, 69] (normal_endpoints 738) h]
    exact Submodule.zero_mem _
lemma extension_739_22 : a k 22*normalRep k 739=normalRep k 846 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 70] 22).symm
lemma extension_739_23 : a k 23*normalRep k 739=(-normalRep k 845) := by
  change a k 23*walk k 31 [41, 43, 47, 7, 17, 21, 70]=(-walk k 31 [41, 43, 47, 7, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_613 (a k) (relation_zero k) (e k 31)
lemma arrow_span_739 (b : Fin 75) : a k b*normalRep k 739 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_739_22 k]
      exact normal_mem k 846
    · rw [extension_739_23 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 845)
  · rw [show a k b*normalRep k 739=0 from arrow_incompatible k b 31 19 [41, 43, 47, 7, 17, 21, 70] (normal_endpoints 739) h]
    exact Submodule.zero_mem _
lemma extension_740_72 : a k 72*normalRep k 740=normalRep k 847 := by
  exact (walk_snoc k 31 [41, 43, 48, 51, 64, 36, 71] 72).symm
lemma extension_740_73 : a k 73*normalRep k 740=(-normalRep k 845) := by
  change a k 73*walk k 31 [41, 43, 48, 51, 64, 36, 71]=(-walk k 31 [41, 43, 47, 7, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_614 (a k) (relation_zero k) (e k 31)
lemma arrow_span_740 (b : Fin 75) : a k b*normalRep k 740 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_740_72 k]
      exact normal_mem k 847
    · rw [extension_740_73 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 845)
  · rw [show a k b*normalRep k 740=0 from arrow_incompatible k b 31 44 [41, 43, 48, 51, 64, 36, 71] (normal_endpoints 740) h]
    exact Submodule.zero_mem _
lemma extension_741_2 : a k 2*normalRep k 741=normalRep k 848 := by
  exact (walk_snoc k 31 [41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_741 (b : Fin 75) : a k b*normalRep k 741 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_741_2 k]
      exact normal_mem k 848
  · rw [show a k b*normalRep k 741=0 from arrow_incompatible k b 31 2 [41, 44, 57, 5, 63, 20, 30] (normal_endpoints 741) h]
    exact Submodule.zero_mem _
lemma extension_742_66 : a k 66*normalRep k 742=normalRep k 849 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8] 66).symm
lemma extension_742_67 : a k 67*normalRep k 742=0 := by
  change a k 67*walk k 32 [43, 47, 7, 17, 21, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_541 (a k) (relation_zero k) (e k 32)
lemma extension_742_68 : a k 68*normalRep k 742=normalRep k 850 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8] 68).symm
lemma arrow_span_742 (b : Fin 75) : a k b*normalRep k 742 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_742_66 k]
      exact normal_mem k 849
    · rw [extension_742_67 k]
      exact Submodule.zero_mem _
    · rw [extension_742_68 k]
      exact normal_mem k 850
  · rw [show a k b*normalRep k 742=0 from arrow_incompatible k b 32 42 [43, 47, 7, 17, 21, 69, 8] (normal_endpoints 742) h]
    exact Submodule.zero_mem _
lemma extension_743_3 : a k 3*normalRep k 743=normalRep k 850 := by
  change a k 3*walk k 32 [43, 47, 7, 17, 21, 70, 22]=walk k 32 [43, 47, 7, 17, 21, 69, 8, 68]
  rw [← walk_snoc]
  exact Universal.mul_reduced_561 (a k) (relation_zero k) (e k 32)
lemma arrow_span_743 (b : Fin 75) : a k b*normalRep k 743 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_743_3 k]
      exact normal_mem k 850
  · rw [show a k b*normalRep k 743=0 from arrow_incompatible k b 32 3 [43, 47, 7, 17, 21, 70, 22] (normal_endpoints 743) h]
    exact Submodule.zero_mem _
lemma extension_744_37 : a k 37*normalRep k 744=(-normalRep k 849) := by
  change a k 37*walk k 32 [43, 48, 51, 64, 36, 71, 72]=(-walk k 32 [43, 47, 7, 17, 21, 69, 8, 66])
  rw [← walk_snoc]
  exact Universal.mul_reduced_618 (a k) (relation_zero k) (e k 32)
lemma extension_744_38 : a k 38*normalRep k 744=normalRep k 851 := by
  exact (walk_snoc k 32 [43, 48, 51, 64, 36, 71, 72] 38).symm
lemma arrow_span_744 (b : Fin 75) : a k b*normalRep k 744 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_744_37 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 849)
    · rw [extension_744_38 k]
      exact normal_mem k 851
  · rw [show a k b*normalRep k 744=0 from arrow_incompatible k b 32 29 [43, 48, 51, 64, 36, 71, 72] (normal_endpoints 744) h]
    exact Submodule.zero_mem _
lemma extension_745_0 : a k 0*normalRep k 745=normalRep k 852 := by
  exact (walk_snoc k 32 [44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_745 (b : Fin 75) : a k b*normalRep k 745 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_745_0 k]
      exact normal_mem k 852
  · rw [show a k b*normalRep k 745=0 from arrow_incompatible k b 32 0 [44, 57, 5, 63, 20, 30, 2] (normal_endpoints 745) h]
    exact Submodule.zero_mem _
lemma extension_746_66 : a k 66*normalRep k 746=normalRep k 853 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8] 66).symm
lemma extension_746_67 : a k 67*normalRep k 746=0 := by
  change a k 67*walk k 33 [45, 6, 7, 17, 21, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_542 (a k) (relation_zero k) (e k 33)
lemma extension_746_68 : a k 68*normalRep k 746=normalRep k 854 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8] 68).symm
lemma arrow_span_746 (b : Fin 75) : a k b*normalRep k 746 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_746_66 k]
      exact normal_mem k 853
    · rw [extension_746_67 k]
      exact Submodule.zero_mem _
    · rw [extension_746_68 k]
      exact normal_mem k 854
  · rw [show a k b*normalRep k 746=0 from arrow_incompatible k b 33 42 [45, 6, 7, 17, 21, 69, 8] (normal_endpoints 746) h]
    exact Submodule.zero_mem _
lemma extension_747_3 : a k 3*normalRep k 747=normalRep k 854 := by
  change a k 3*walk k 33 [45, 6, 7, 17, 21, 70, 22]=walk k 33 [45, 6, 7, 17, 21, 69, 8, 68]
  rw [← walk_snoc]
  exact Universal.mul_reduced_562 (a k) (relation_zero k) (e k 33)
lemma arrow_span_747 (b : Fin 75) : a k b*normalRep k 747 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_747_3 k]
      exact normal_mem k 854
  · rw [show a k b*normalRep k 747=0 from arrow_incompatible k b 33 3 [45, 6, 7, 17, 21, 70, 22] (normal_endpoints 747) h]
    exact Submodule.zero_mem _
lemma extension_748_37 : a k 37*normalRep k 748=(-normalRep k 853) := by
  change a k 37*walk k 33 [46, 48, 51, 64, 36, 71, 72]=(-walk k 33 [45, 6, 7, 17, 21, 69, 8, 66])
  rw [← walk_snoc]
  exact Universal.mul_reduced_619 (a k) (relation_zero k) (e k 33)
lemma extension_748_38 : a k 38*normalRep k 748=normalRep k 855 := by
  exact (walk_snoc k 33 [46, 48, 51, 64, 36, 71, 72] 38).symm
lemma arrow_span_748 (b : Fin 75) : a k b*normalRep k 748 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_748_37 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 853)
    · rw [extension_748_38 k]
      exact normal_mem k 855
  · rw [show a k b*normalRep k 748=0 from arrow_incompatible k b 33 29 [46, 48, 51, 64, 36, 71, 72] (normal_endpoints 748) h]
    exact Submodule.zero_mem _
lemma extension_749_24 : a k 24*normalRep k 749=normalRep k 856 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66] 24).symm
lemma extension_749_25 : a k 25*normalRep k 749=normalRep k 857 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66] 25).symm
lemma arrow_span_749 (b : Fin 75) : a k b*normalRep k 749 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_749_24 k]
      exact normal_mem k 856
    · rw [extension_749_25 k]
      exact normal_mem k 857
  · rw [show a k b*normalRep k 749=0 from arrow_incompatible k b 34 20 [47, 7, 17, 21, 69, 8, 66] (normal_endpoints 749) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
