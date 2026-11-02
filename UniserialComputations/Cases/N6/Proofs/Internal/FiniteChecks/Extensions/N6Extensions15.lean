import N6NormalData
import N6Reduced8
import N6Reduced9
import N6Reduced10
import N6Reduced11
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_750_39 : a k 39*normalRep k 750=0 := by
  change a k 39*walk k 34 [47, 7, 17, 21, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_528 (a k) (relation_zero k) (e k 34)
lemma extension_750_40 : a k 40*normalRep k 750=(-normalRep k 857) := by
  change a k 40*walk k 34 [47, 7, 17, 21, 69, 8, 68]=(-walk k 34 [47, 7, 17, 21, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_610 (a k) (relation_zero k) (e k 34)
lemma arrow_span_750 (b : Fin 75) : a k b*normalRep k 750 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_750_39 k]
      exact Submodule.zero_mem _
    · rw [extension_750_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 857)
  · rw [show a k b*normalRep k 750=0 from arrow_incompatible k b 34 30 [47, 7, 17, 21, 69, 8, 68] (normal_endpoints 750) h]
    exact Submodule.zero_mem _
lemma extension_751_28 : a k 28*normalRep k 751=normalRep k 858 := by
  exact (walk_snoc k 34 [48, 51, 64, 36, 71, 72, 38] 28).symm
lemma extension_751_29 : a k 29*normalRep k 751=(-normalRep k 856) := by
  change a k 29*walk k 34 [48, 51, 64, 36, 71, 72, 38]=(-walk k 34 [47, 7, 17, 21, 69, 8, 66, 24])
  rw [← walk_snoc]
  exact Universal.mul_reduced_578 (a k) (relation_zero k) (e k 34)
lemma arrow_span_751 (b : Fin 75) : a k b*normalRep k 751 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_751_28 k]
      exact normal_mem k 858
    · rw [extension_751_29 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 856)
  · rw [show a k b*normalRep k 751=0 from arrow_incompatible k b 34 23 [48, 51, 64, 36, 71, 72, 38] (normal_endpoints 751) h]
    exact Submodule.zero_mem _
lemma extension_752_41 : a k 41*normalRep k 752=normalRep k 859 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_752_42 : a k 42*normalRep k 752=0 := by
  change a k 42*walk k 35 [49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_543 (a k) (relation_zero k) (e k 35)
lemma arrow_span_752 (b : Fin 75) : a k b*normalRep k 752 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_752_41 k]
      exact normal_mem k 859
    · rw [extension_752_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 752=0 from arrow_incompatible k b 35 31 [49, 69, 8, 66, 24, 18, 9] (normal_endpoints 752) h]
    exact Submodule.zero_mem _
lemma extension_753_54 : a k 54*normalRep k 753=normalRep k 860 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_753_55 : a k 55*normalRep k 753=0 := by
  change a k 55*walk k 35 [49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_534 (a k) (relation_zero k) (e k 35)
lemma extension_753_56 : a k 56*normalRep k 753=normalRep k 859 := by
  change a k 56*walk k 35 [49, 69, 8, 66, 24, 19, 53]=walk k 35 [49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_592 (a k) (relation_zero k) (e k 35)
lemma arrow_span_753 (b : Fin 75) : a k b*normalRep k 753 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_753_54 k]
      exact normal_mem k 860
    · rw [extension_753_55 k]
      exact Submodule.zero_mem _
    · rw [extension_753_56 k]
      exact normal_mem k 859
  · rw [show a k b*normalRep k 753=0 from arrow_incompatible k b 35 38 [49, 69, 8, 66, 24, 19, 53] (normal_endpoints 753) h]
    exact Submodule.zero_mem _
lemma extension_754_18 : a k 18*normalRep k 754=normalRep k 861 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24] 18).symm
lemma extension_754_19 : a k 19*normalRep k 754=normalRep k 862 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24] 19).symm
lemma arrow_span_754 (b : Fin 75) : a k b*normalRep k 754 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_754_18 k]
      exact normal_mem k 861
    · rw [extension_754_19 k]
      exact normal_mem k 862
  · rw [show a k b*normalRep k 754=0 from arrow_incompatible k b 36 17 [50, 17, 21, 69, 8, 66, 24] (normal_endpoints 754) h]
    exact Submodule.zero_mem _
lemma extension_755_60 : a k 60*normalRep k 755=normalRep k 863 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 25] 60).symm
lemma extension_755_61 : a k 61*normalRep k 755=0 := by
  change a k 61*walk k 36 [50, 17, 21, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_565 (a k) (relation_zero k) (e k 36)
lemma extension_755_62 : a k 62*normalRep k 755=normalRep k 862 := by
  change a k 62*walk k 36 [50, 17, 21, 69, 8, 66, 25]=walk k 36 [50, 17, 21, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_568 (a k) (relation_zero k) (e k 36)
lemma arrow_span_755 (b : Fin 75) : a k b*normalRep k 755 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_755_60 k]
      exact normal_mem k 863
    · rw [extension_755_61 k]
      exact Submodule.zero_mem _
    · rw [extension_755_62 k]
      exact normal_mem k 862
  · rw [show a k b*normalRep k 755=0 from arrow_incompatible k b 36 40 [50, 17, 21, 69, 8, 66, 25] (normal_endpoints 755) h]
    exact Submodule.zero_mem _
lemma extension_756_14 : a k 14*normalRep k 756=(-normalRep k 861) := by
  change a k 14*walk k 36 [51, 64, 36, 71, 72, 38, 28]=(-walk k 36 [50, 17, 21, 69, 8, 66, 24, 18])
  rw [← walk_snoc]
  exact Universal.mul_reduced_571 (a k) (relation_zero k) (e k 36)
lemma arrow_span_756 (b : Fin 75) : a k b*normalRep k 756 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_756_14 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 861)
  · rw [show a k b*normalRep k 756=0 from arrow_incompatible k b 36 14 [51, 64, 36, 71, 72, 38, 28] (normal_endpoints 756) h]
    exact Submodule.zero_mem _
lemma extension_757_69 : a k 69*normalRep k 757=normalRep k 864 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21] 69).symm
lemma extension_757_70 : a k 70*normalRep k 757=normalRep k 865 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21] 70).symm
lemma extension_757_71 : a k 71*normalRep k 757=0 := by
  change a k 71*walk k 37 [52, 41, 43, 47, 7, 17, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_559 (a k) (relation_zero k) (e k 37)
lemma arrow_span_757 (b : Fin 75) : a k b*normalRep k 757 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_757_69 k]
      exact normal_mem k 864
    · rw [extension_757_70 k]
      exact normal_mem k 865
    · rw [extension_757_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 757=0 from arrow_incompatible k b 37 43 [52, 41, 43, 47, 7, 17, 21] (normal_endpoints 757) h]
    exact Submodule.zero_mem _
lemma extension_758_69 : a k 69*normalRep k 758=0 := by
  change a k 69*walk k 37 [52, 41, 43, 48, 51, 64, 36]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_577 (a k) (relation_zero k) (e k 37)
lemma extension_758_70 : a k 70*normalRep k 758=normalRep k 865 := by
  change a k 70*walk k 37 [52, 41, 43, 48, 51, 64, 36]=walk k 37 [52, 41, 43, 47, 7, 17, 21, 70]
  rw [← walk_snoc]
  exact Universal.mul_reduced_586 (a k) (relation_zero k) (e k 37)
lemma extension_758_71 : a k 71*normalRep k 758=normalRep k 866 := by
  exact (walk_snoc k 37 [52, 41, 43, 48, 51, 64, 36] 71).symm
lemma arrow_span_758 (b : Fin 75) : a k b*normalRep k 758 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_758_69 k]
      exact Submodule.zero_mem _
    · rw [extension_758_70 k]
      exact normal_mem k 865
    · rw [extension_758_71 k]
      exact normal_mem k 866
  · rw [show a k b*normalRep k 758=0 from arrow_incompatible k b 37 43 [52, 41, 43, 48, 51, 64, 36] (normal_endpoints 758) h]
    exact Submodule.zero_mem _
lemma extension_759_30 : a k 30*normalRep k 759=normalRep k 867 := by
  exact (walk_snoc k 37 [52, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_759_31 : a k 31*normalRep k 759=0 := by
  change a k 31*walk k 37 [52, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_557 (a k) (relation_zero k) (e k 37)
lemma arrow_span_759 (b : Fin 75) : a k b*normalRep k 759 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_759_30 k]
      exact normal_mem k 867
    · rw [extension_759_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 759=0 from arrow_incompatible k b 37 24 [52, 41, 44, 57, 5, 63, 20] (normal_endpoints 759) h]
    exact Submodule.zero_mem _
lemma extension_760_2 : a k 2*normalRep k 760=normalRep k 868 := by
  exact (walk_snoc k 38 [54, 15, 1, 34, 63, 20, 30] 2).symm
lemma arrow_span_760 (b : Fin 75) : a k b*normalRep k 760 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_760_2 k]
      exact normal_mem k 868
  · rw [show a k b*normalRep k 760=0 from arrow_incompatible k b 38 2 [54, 15, 1, 34, 63, 20, 30] (normal_endpoints 760) h]
    exact Submodule.zero_mem _
lemma extension_761_8 : a k 8*normalRep k 761=normalRep k 869 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_761 (b : Fin 75) : a k b*normalRep k 761 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_761_8 k]
      exact normal_mem k 869
  · rw [show a k b*normalRep k 761=0 from arrow_incompatible k b 38 8 [55, 27, 58, 33, 13, 49, 69] (normal_endpoints 761) h]
    exact Submodule.zero_mem _
lemma extension_762_72 : a k 72*normalRep k 762=normalRep k 870 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 71] 72).symm
lemma extension_762_73 : a k 73*normalRep k 762=normalRep k 869 := by
  change a k 73*walk k 38 [55, 27, 58, 33, 13, 49, 71]=walk k 38 [55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_615 (a k) (relation_zero k) (e k 38)
lemma arrow_span_762 (b : Fin 75) : a k b*normalRep k 762 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_762_72 k]
      exact normal_mem k 870
    · rw [extension_762_73 k]
      exact normal_mem k 869
  · rw [show a k b*normalRep k 762=0 from arrow_incompatible k b 38 44 [55, 27, 58, 33, 13, 49, 71] (normal_endpoints 762) h]
    exact Submodule.zero_mem _
lemma extension_763_22 : a k 22*normalRep k 763=normalRep k 871 := by
  exact (walk_snoc k 38 [55, 27, 58, 34, 63, 21, 70] 22).symm
lemma extension_763_23 : a k 23*normalRep k 763=normalRep k 869 := by
  change a k 23*walk k 38 [55, 27, 58, 34, 63, 21, 70]=walk k 38 [55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_616 (a k) (relation_zero k) (e k 38)
lemma arrow_span_763 (b : Fin 75) : a k b*normalRep k 763 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_763_22 k]
      exact normal_mem k 871
    · rw [extension_763_23 k]
      exact normal_mem k 869
  · rw [show a k b*normalRep k 763=0 from arrow_incompatible k b 38 19 [55, 27, 58, 34, 63, 21, 70] (normal_endpoints 763) h]
    exact Submodule.zero_mem _
lemma arrow_span_764 (b : Fin 75) : a k b*normalRep k 764 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 764=0 from arrow_incompatible k b 39 46 [57, 5, 63, 20, 30, 2, 0] (normal_endpoints 764) h]
    exact Submodule.zero_mem _
lemma extension_765_24 : a k 24*normalRep k 765=normalRep k 872 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_765_25 : a k 25*normalRep k 765=normalRep k 873 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_765 (b : Fin 75) : a k b*normalRep k 765 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_765_24 k]
      exact normal_mem k 872
    · rw [extension_765_25 k]
      exact normal_mem k 873
  · rw [show a k b*normalRep k 765=0 from arrow_incompatible k b 39 20 [58, 33, 13, 49, 69, 8, 66] (normal_endpoints 765) h]
    exact Submodule.zero_mem _
lemma extension_766_39 : a k 39*normalRep k 766=0 := by
  change a k 39*walk k 39 [58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_529 (a k) (relation_zero k) (e k 39)
lemma extension_766_40 : a k 40*normalRep k 766=(-normalRep k 873) := by
  change a k 40*walk k 39 [58, 33, 13, 49, 69, 8, 68]=(-walk k 39 [58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_611 (a k) (relation_zero k) (e k 39)
lemma arrow_span_766 (b : Fin 75) : a k b*normalRep k 766 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_766_39 k]
      exact Submodule.zero_mem _
    · rw [extension_766_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 873)
  · rw [show a k b*normalRep k 766=0 from arrow_incompatible k b 39 30 [58, 33, 13, 49, 69, 8, 68] (normal_endpoints 766) h]
    exact Submodule.zero_mem _
lemma extension_767_28 : a k 28*normalRep k 767=normalRep k 874 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_767_29 : a k 29*normalRep k 767=normalRep k 872 := by
  change a k 29*walk k 39 [58, 33, 13, 49, 71, 72, 38]=walk k 39 [58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_579 (a k) (relation_zero k) (e k 39)
lemma arrow_span_767 (b : Fin 75) : a k b*normalRep k 767 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_767_28 k]
      exact normal_mem k 874
    · rw [extension_767_29 k]
      exact normal_mem k 872
  · rw [show a k b*normalRep k 767=0 from arrow_incompatible k b 39 23 [58, 33, 13, 49, 71, 72, 38] (normal_endpoints 767) h]
    exact Submodule.zero_mem _
lemma extension_768_20 : a k 20*normalRep k 768=normalRep k 875 := by
  exact (walk_snoc k 40 [60, 4, 54, 15, 1, 34, 63] 20).symm
lemma extension_768_21 : a k 21*normalRep k 768=0 := by
  change a k 21*walk k 40 [60, 4, 54, 15, 1, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_607 (a k) (relation_zero k) (e k 40)
lemma arrow_span_768 (b : Fin 75) : a k b*normalRep k 768 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_768_20 k]
      exact normal_mem k 875
    · rw [extension_768_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 768=0 from arrow_incompatible k b 40 18 [60, 4, 54, 15, 1, 34, 63] (normal_endpoints 768) h]
    exact Submodule.zero_mem _
lemma extension_769_49 : a k 49*normalRep k 769=normalRep k 876 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13] 49).symm
lemma arrow_span_769 (b : Fin 75) : a k b*normalRep k 769 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_769_49 k]
      exact normal_mem k 876
  · rw [show a k b*normalRep k 769=0 from arrow_incompatible k b 40 35 [61, 35, 55, 27, 58, 33, 13] (normal_endpoints 769) h]
    exact Submodule.zero_mem _
lemma extension_770_20 : a k 20*normalRep k 770=0 := by
  change a k 20*walk k 40 [61, 35, 55, 27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_551 (a k) (relation_zero k) (e k 40)
lemma extension_770_21 : a k 21*normalRep k 770=normalRep k 877 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 34, 63] 21).symm
lemma arrow_span_770 (b : Fin 75) : a k b*normalRep k 770 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_770_20 k]
      exact Submodule.zero_mem _
    · rw [extension_770_21 k]
      exact normal_mem k 877
  · rw [show a k b*normalRep k 770=0 from arrow_incompatible k b 40 18 [61, 35, 55, 27, 58, 34, 63] (normal_endpoints 770) h]
    exact Submodule.zero_mem _
lemma extension_771_36 : a k 36*normalRep k 771=normalRep k 877 + normalRep k 876 := by
  change a k 36*walk k 40 [61, 35, 55, 27, 58, 34, 64]=walk k 40 [61, 35, 55, 27, 58, 34, 63, 21] + walk k 40 [61, 35, 55, 27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_608 (a k) (relation_zero k) (e k 40)
lemma arrow_span_771 (b : Fin 75) : a k b*normalRep k 771 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_771_36 k]
      exact (normalSpan k).add_mem (normal_mem k 877) (normal_mem k 876)
  · rw [show a k b*normalRep k 771=0 from arrow_incompatible k b 40 28 [61, 35, 55, 27, 58, 34, 64] (normal_endpoints 771) h]
    exact Submodule.zero_mem _
lemma extension_772_9 : a k 9*normalRep k 772=normalRep k 878 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_772 (b : Fin 75) : a k b*normalRep k 772 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_772_9 k]
      exact normal_mem k 878
  · rw [show a k b*normalRep k 772=0 from arrow_incompatible k b 41 9 [63, 21, 69, 8, 66, 24, 18] (normal_endpoints 772) h]
    exact Submodule.zero_mem _
lemma extension_773_52 : a k 52*normalRep k 773=normalRep k 878 := by
  change a k 52*walk k 41 [63, 21, 69, 8, 66, 24, 19]=walk k 41 [63, 21, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_554 (a k) (relation_zero k) (e k 41)
lemma extension_773_53 : a k 53*normalRep k 773=normalRep k 879 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_773 (b : Fin 75) : a k b*normalRep k 773 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_773_52 k]
      exact normal_mem k 878
    · rw [extension_773_53 k]
      exact normal_mem k 879
  · rw [show a k b*normalRep k 773=0 from arrow_incompatible k b 41 37 [63, 21, 69, 8, 66, 24, 19] (normal_endpoints 773) h]
    exact Submodule.zero_mem _
lemma extension_774_4 : a k 4*normalRep k 774=normalRep k 879 := by
  change a k 4*walk k 41 [63, 21, 69, 8, 66, 25, 60]=walk k 41 [63, 21, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_603 (a k) (relation_zero k) (e k 41)
lemma arrow_span_774 (b : Fin 75) : a k b*normalRep k 774 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_774_4 k]
      exact normal_mem k 879
  · rw [show a k b*normalRep k 774=0 from arrow_incompatible k b 41 4 [63, 21, 69, 8, 66, 25, 60] (normal_endpoints 774) h]
    exact Submodule.zero_mem _
lemma extension_775_5 : a k 5*normalRep k 775=normalRep k 880 := by
  exact (walk_snoc k 42 [66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_775 (b : Fin 75) : a k b*normalRep k 775 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_775_5 k]
      exact normal_mem k 880
  · rw [show a k b*normalRep k 775=0 from arrow_incompatible k b 42 5 [66, 24, 18, 9, 41, 44, 57] (normal_endpoints 775) h]
    exact Submodule.zero_mem _
lemma extension_776_33 : a k 33*normalRep k 776=0 := by
  change a k 33*walk k 42 [66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_523 (a k) (relation_zero k) (e k 42)
lemma extension_776_34 : a k 34*normalRep k 776=normalRep k 880 := by
  change a k 34*walk k 42 [66, 24, 18, 9, 41, 44, 58]=walk k 42 [66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_598 (a k) (relation_zero k) (e k 42)
lemma arrow_span_776 (b : Fin 75) : a k b*normalRep k 776 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_776_33 k]
      exact Submodule.zero_mem _
    · rw [extension_776_34 k]
      exact normal_mem k 880
  · rw [show a k b*normalRep k 776=0 from arrow_incompatible k b 42 26 [66, 24, 18, 9, 41, 44, 58] (normal_endpoints 776) h]
    exact Submodule.zero_mem _
lemma extension_777_33 : a k 33*normalRep k 777=normalRep k 881 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58] 33).symm
lemma extension_777_34 : a k 34*normalRep k 777=normalRep k 882 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58] 34).symm
lemma arrow_span_777 (b : Fin 75) : a k b*normalRep k 777 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_777_33 k]
      exact normal_mem k 881
    · rw [extension_777_34 k]
      exact normal_mem k 882
  · rw [show a k b*normalRep k 777=0 from arrow_incompatible k b 42 26 [67, 32, 61, 35, 55, 27, 58] (normal_endpoints 777) h]
    exact Submodule.zero_mem _
lemma extension_778_50 : a k 50*normalRep k 778=normalRep k 883 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 59] 50).symm
lemma extension_778_51 : a k 51*normalRep k 778=normalRep k 882 := by
  change a k 51*walk k 42 [67, 32, 61, 35, 55, 27, 59]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_599 (a k) (relation_zero k) (e k 42)
lemma arrow_span_778 (b : Fin 75) : a k b*normalRep k 778 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_778_50 k]
      exact normal_mem k 883
    · rw [extension_778_51 k]
      exact normal_mem k 882
  · rw [show a k b*normalRep k 778=0 from arrow_incompatible k b 42 36 [67, 32, 61, 35, 55, 27, 59] (normal_endpoints 778) h]
    exact Submodule.zero_mem _
lemma extension_779_7 : a k 7*normalRep k 779=normalRep k 883 := by
  change a k 7*walk k 42 [67, 32, 61, 35, 56, 43, 47]=walk k 42 [67, 32, 61, 35, 55, 27, 59, 50]
  rw [← walk_snoc]
  exact Universal.mul_reduced_584 (a k) (relation_zero k) (e k 42)
lemma arrow_span_779 (b : Fin 75) : a k b*normalRep k 779 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_779_7 k]
      exact normal_mem k 883
  · rw [show a k b*normalRep k 779=0 from arrow_incompatible k b 42 7 [67, 32, 61, 35, 56, 43, 47] (normal_endpoints 779) h]
    exact Submodule.zero_mem _
lemma extension_780_43 : a k 43*normalRep k 780=0 := by
  change a k 43*walk k 43 [69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_535 (a k) (relation_zero k) (e k 43)
lemma extension_780_44 : a k 44*normalRep k 780=normalRep k 884 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_780 (b : Fin 75) : a k b*normalRep k 780 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_780_43 k]
      exact Submodule.zero_mem _
    · rw [extension_780_44 k]
      exact normal_mem k 884
  · rw [show a k b*normalRep k 780=0 from arrow_incompatible k b 43 32 [69, 8, 66, 24, 18, 9, 41] (normal_endpoints 780) h]
    exact Submodule.zero_mem _
lemma extension_781_15 : a k 15*normalRep k 781=normalRep k 885 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_781_16 : a k 16*normalRep k 781=normalRep k 884 := by
  change a k 16*walk k 43 [69, 8, 66, 24, 19, 53, 54]=walk k 43 [69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_594 (a k) (relation_zero k) (e k 43)
lemma arrow_span_781 (b : Fin 75) : a k b*normalRep k 781 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_781_15 k]
      exact normal_mem k 885
    · rw [extension_781_16 k]
      exact normal_mem k 884
  · rw [show a k b*normalRep k 781=0 from arrow_incompatible k b 43 15 [69, 8, 66, 24, 19, 53, 54] (normal_endpoints 781) h]
    exact Submodule.zero_mem _
lemma extension_782_15 : a k 15*normalRep k 782=normalRep k 886 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 60, 4, 54] 15).symm
lemma extension_782_16 : a k 16*normalRep k 782=normalRep k 887 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 60, 4, 54] 16).symm
lemma arrow_span_782 (b : Fin 75) : a k b*normalRep k 782 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_782_15 k]
      exact normal_mem k 886
    · rw [extension_782_16 k]
      exact normal_mem k 887
  · rw [show a k b*normalRep k 782=0 from arrow_incompatible k b 43 15 [70, 22, 3, 40, 60, 4, 54] (normal_endpoints 782) h]
    exact Submodule.zero_mem _
lemma extension_783_43 : a k 43*normalRep k 783=0 := by
  change a k 43*walk k 43 [70, 22, 3, 40, 60, 4, 56]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_536 (a k) (relation_zero k) (e k 43)
lemma extension_783_44 : a k 44*normalRep k 783=normalRep k 887 := by
  change a k 44*walk k 43 [70, 22, 3, 40, 60, 4, 56]=walk k 43 [70, 22, 3, 40, 60, 4, 54, 16]
  rw [← walk_snoc]
  exact Universal.mul_reduced_595 (a k) (relation_zero k) (e k 43)
lemma arrow_span_783 (b : Fin 75) : a k b*normalRep k 783 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_783_43 k]
      exact Submodule.zero_mem _
    · rw [extension_783_44 k]
      exact normal_mem k 887
  · rw [show a k b*normalRep k 783=0 from arrow_incompatible k b 43 32 [70, 22, 3, 40, 60, 4, 56] (normal_endpoints 783) h]
    exact Submodule.zero_mem _
lemma extension_784_57 : a k 57*normalRep k 784=normalRep k 888 := by
  exact (walk_snoc k 44 [72, 37, 24, 18, 9, 41, 44] 57).symm
lemma extension_784_58 : a k 58*normalRep k 784=normalRep k 889 := by
  exact (walk_snoc k 44 [72, 37, 24, 18, 9, 41, 44] 58).symm
lemma extension_784_59 : a k 59*normalRep k 784=0 := by
  change a k 59*walk k 44 [72, 37, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_549 (a k) (relation_zero k) (e k 44)
lemma arrow_span_784 (b : Fin 75) : a k b*normalRep k 784 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_784_57 k]
      exact normal_mem k 888
    · rw [extension_784_58 k]
      exact normal_mem k 889
    · rw [extension_784_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 784=0 from arrow_incompatible k b 44 39 [72, 37, 24, 18, 9, 41, 44] (normal_endpoints 784) h]
    exact Submodule.zero_mem _
lemma extension_785_1 : a k 1*normalRep k 785=normalRep k 889 := by
  change a k 1*walk k 44 [72, 37, 24, 19, 53, 54, 15]=walk k 44 [72, 37, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_546 (a k) (relation_zero k) (e k 44)
lemma arrow_span_785 (b : Fin 75) : a k b*normalRep k 785 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_785_1 k]
      exact normal_mem k 889
  · rw [show a k b*normalRep k 785=0 from arrow_incompatible k b 44 1 [72, 37, 24, 19, 53, 54, 15] (normal_endpoints 785) h]
    exact Submodule.zero_mem _
lemma extension_786_57 : a k 57*normalRep k 786=0 := by
  change a k 57*walk k 44 [73, 67, 32, 61, 35, 55, 27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_569 (a k) (relation_zero k) (e k 44)
lemma extension_786_58 : a k 58*normalRep k 786=normalRep k 890 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27] 58).symm
lemma extension_786_59 : a k 59*normalRep k 786=normalRep k 891 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27] 59).symm
lemma arrow_span_786 (b : Fin 75) : a k b*normalRep k 786 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_786_57 k]
      exact Submodule.zero_mem _
    · rw [extension_786_58 k]
      exact normal_mem k 890
    · rw [extension_786_59 k]
      exact normal_mem k 891
  · rw [show a k b*normalRep k 786=0 from arrow_incompatible k b 44 39 [73, 67, 32, 61, 35, 55, 27] (normal_endpoints 786) h]
    exact Submodule.zero_mem _
lemma extension_787_47 : a k 47*normalRep k 787=normalRep k 892 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 56, 43] 47).symm
lemma extension_787_48 : a k 48*normalRep k 787=normalRep k 891 := by
  change a k 48*walk k 44 [73, 67, 32, 61, 35, 56, 43]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 59]
  rw [← walk_snoc]
  exact Universal.mul_reduced_582 (a k) (relation_zero k) (e k 44)
lemma arrow_span_787 (b : Fin 75) : a k b*normalRep k 787 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_787_47 k]
      exact normal_mem k 892
    · rw [extension_787_48 k]
      exact normal_mem k 891
  · rw [show a k b*normalRep k 787=0 from arrow_incompatible k b 44 34 [73, 67, 32, 61, 35, 56, 43] (normal_endpoints 787) h]
    exact Submodule.zero_mem _
lemma extension_788_6 : a k 6*normalRep k 788=normalRep k 892 := by
  change a k 6*walk k 44 [73, 67, 32, 62, 52, 42, 45]=walk k 44 [73, 67, 32, 61, 35, 56, 43, 47]
  rw [← walk_snoc]
  exact Universal.mul_reduced_583 (a k) (relation_zero k) (e k 44)
lemma arrow_span_788 (b : Fin 75) : a k b*normalRep k 788 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_788_6 k]
      exact normal_mem k 892
  · rw [show a k b*normalRep k 788=0 from arrow_incompatible k b 44 6 [73, 67, 32, 62, 52, 42, 45] (normal_endpoints 788) h]
    exact Submodule.zero_mem _
lemma extension_789_32 : a k 32*normalRep k 789=normalRep k 893 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67] 32).symm
lemma arrow_span_789 (b : Fin 75) : a k b*normalRep k 789 ∈ normalSpan k := by
  by_cases h : arrowSource b=25
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [32] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_789_32 k]
      exact normal_mem k 893
  · rw [show a k b*normalRep k 789=0 from arrow_incompatible k b 45 25 [74, 10, 11, 26, 31, 73, 67] (normal_endpoints 789) h]
    exact Submodule.zero_mem _
lemma extension_790_39 : a k 39*normalRep k 790=normalRep k 894 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 68] 39).symm
lemma extension_790_40 : a k 40*normalRep k 790=normalRep k 893 := by
  change a k 40*walk k 45 [74, 10, 11, 26, 31, 73, 68]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32]
  rw [← walk_snoc]
  exact Universal.mul_reduced_612 (a k) (relation_zero k) (e k 45)
lemma arrow_span_790 (b : Fin 75) : a k b*normalRep k 790 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_790_39 k]
      exact normal_mem k 894
    · rw [extension_790_40 k]
      exact normal_mem k 893
  · rw [show a k b*normalRep k 790=0 from arrow_incompatible k b 45 30 [74, 10, 11, 26, 31, 73, 68] (normal_endpoints 790) h]
    exact Submodule.zero_mem _
lemma extension_791_63 : a k 63*normalRep k 791=normalRep k 895 := by
  exact (walk_snoc k 3 [3, 40, 60, 4, 54, 15, 1, 34] 63).symm
lemma extension_791_64 : a k 64*normalRep k 791=0 := by
  change a k 64*walk k 3 [3, 40, 60, 4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_623 (a k) (relation_zero k) (e k 3)
lemma extension_791_65 : a k 65*normalRep k 791=0 := by
  change a k 65*walk k 3 [3, 40, 60, 4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_637 (a k) (relation_zero k) (e k 3)
lemma arrow_span_791 (b : Fin 75) : a k b*normalRep k 791 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_791_63 k]
      exact normal_mem k 895
    · rw [extension_791_64 k]
      exact Submodule.zero_mem _
    · rw [extension_791_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 791=0 from arrow_incompatible k b 3 41 [3, 40, 60, 4, 54, 15, 1, 34] (normal_endpoints 791) h]
    exact Submodule.zero_mem _
lemma extension_792_2 : a k 2*normalRep k 792=normalRep k 896 := by
  exact (walk_snoc k 4 [4, 54, 15, 1, 34, 63, 20, 30] 2).symm
lemma arrow_span_792 (b : Fin 75) : a k b*normalRep k 792 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_792_2 k]
      exact normal_mem k 896
  · rw [show a k b*normalRep k 792=0 from arrow_incompatible k b 4 2 [4, 54, 15, 1, 34, 63, 20, 30] (normal_endpoints 792) h]
    exact Submodule.zero_mem _
lemma extension_793_18 : a k 18*normalRep k 793=normalRep k 897 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24] 18).symm
lemma extension_793_19 : a k 19*normalRep k 793=normalRep k 898 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24] 19).symm
lemma arrow_span_793 (b : Fin 75) : a k b*normalRep k 793 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_793_18 k]
      exact normal_mem k 897
    · rw [extension_793_19 k]
      exact normal_mem k 898
  · rw [show a k b*normalRep k 793=0 from arrow_incompatible k b 6 17 [6, 7, 17, 21, 69, 8, 66, 24] (normal_endpoints 793) h]
    exact Submodule.zero_mem _
lemma extension_794_60 : a k 60*normalRep k 794=normalRep k 899 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 25] 60).symm
lemma extension_794_61 : a k 61*normalRep k 794=0 := by
  change a k 61*walk k 6 [6, 7, 17, 21, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_659 (a k) (relation_zero k) (e k 6)
lemma extension_794_62 : a k 62*normalRep k 794=normalRep k 898 := by
  change a k 62*walk k 6 [6, 7, 17, 21, 69, 8, 66, 25]=walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_662 (a k) (relation_zero k) (e k 6)
lemma arrow_span_794 (b : Fin 75) : a k b*normalRep k 794 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_794_60 k]
      exact normal_mem k 899
    · rw [extension_794_61 k]
      exact Submodule.zero_mem _
    · rw [extension_794_62 k]
      exact normal_mem k 898
  · rw [show a k b*normalRep k 794=0 from arrow_incompatible k b 6 40 [6, 7, 17, 21, 69, 8, 66, 25] (normal_endpoints 794) h]
    exact Submodule.zero_mem _
lemma extension_795_9 : a k 9*normalRep k 795=normalRep k 900 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_795 (b : Fin 75) : a k b*normalRep k 795 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_795_9 k]
      exact normal_mem k 900
  · rw [show a k b*normalRep k 795=0 from arrow_incompatible k b 7 9 [7, 17, 21, 69, 8, 66, 24, 18] (normal_endpoints 795) h]
    exact Submodule.zero_mem _
lemma extension_796_52 : a k 52*normalRep k 796=normalRep k 900 := by
  change a k 52*walk k 7 [7, 17, 21, 69, 8, 66, 24, 19]=walk k 7 [7, 17, 21, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_649 (a k) (relation_zero k) (e k 7)
lemma extension_796_53 : a k 53*normalRep k 796=normalRep k 901 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_796 (b : Fin 75) : a k b*normalRep k 796 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_796_52 k]
      exact normal_mem k 900
    · rw [extension_796_53 k]
      exact normal_mem k 901
  · rw [show a k b*normalRep k 796=0 from arrow_incompatible k b 7 37 [7, 17, 21, 69, 8, 66, 24, 19] (normal_endpoints 796) h]
    exact Submodule.zero_mem _
lemma extension_797_4 : a k 4*normalRep k 797=normalRep k 901 := by
  change a k 4*walk k 7 [7, 17, 21, 69, 8, 66, 25, 60]=walk k 7 [7, 17, 21, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_696 (a k) (relation_zero k) (e k 7)
lemma arrow_span_797 (b : Fin 75) : a k b*normalRep k 797 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_797_4 k]
      exact normal_mem k 901
  · rw [show a k b*normalRep k 797=0 from arrow_incompatible k b 7 4 [7, 17, 21, 69, 8, 66, 25, 60] (normal_endpoints 797) h]
    exact Submodule.zero_mem _
lemma extension_798_5 : a k 5*normalRep k 798=normalRep k 902 := by
  exact (walk_snoc k 8 [8, 66, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_798 (b : Fin 75) : a k b*normalRep k 798 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_798_5 k]
      exact normal_mem k 902
  · rw [show a k b*normalRep k 798=0 from arrow_incompatible k b 8 5 [8, 66, 24, 18, 9, 41, 44, 57] (normal_endpoints 798) h]
    exact Submodule.zero_mem _
lemma extension_799_33 : a k 33*normalRep k 799=0 := by
  change a k 33*walk k 8 [8, 66, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_620 (a k) (relation_zero k) (e k 8)
lemma extension_799_34 : a k 34*normalRep k 799=normalRep k 902 := by
  change a k 34*walk k 8 [8, 66, 24, 18, 9, 41, 44, 58]=walk k 8 [8, 66, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_692 (a k) (relation_zero k) (e k 8)
lemma arrow_span_799 (b : Fin 75) : a k b*normalRep k 799 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_799_33 k]
      exact Submodule.zero_mem _
    · rw [extension_799_34 k]
      exact normal_mem k 902
  · rw [show a k b*normalRep k 799=0 from arrow_incompatible k b 8 26 [8, 66, 24, 18, 9, 41, 44, 58] (normal_endpoints 799) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
