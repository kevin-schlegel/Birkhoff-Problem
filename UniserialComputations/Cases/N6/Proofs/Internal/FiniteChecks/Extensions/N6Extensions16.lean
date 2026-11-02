import N6NormalData
import N6Reduced10
import N6Reduced11
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_800_2 : a k 2*normalRep k 800=normalRep k 903 := by
  exact (walk_snoc k 9 [9, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_800 (b : Fin 75) : a k b*normalRep k 800 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_800_2 k]
      exact normal_mem k 903
  · rw [show a k b*normalRep k 800=0 from arrow_incompatible k b 9 2 [9, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 800) h]
    exact Submodule.zero_mem _
lemma extension_801_35 : a k 35*normalRep k 801=normalRep k 904 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 61] 35).symm
lemma arrow_span_801 (b : Fin 75) : a k b*normalRep k 801 ∈ normalSpan k := by
  by_cases h : arrowSource b=27
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [35] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_801_35 k]
      exact normal_mem k 904
  · rw [show a k b*normalRep k 801=0 from arrow_incompatible k b 10 27 [10, 11, 26, 31, 73, 67, 32, 61] (normal_endpoints 801) h]
    exact Submodule.zero_mem _
lemma extension_802_52 : a k 52*normalRep k 802=normalRep k 905 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67, 32, 62] 52).symm
lemma extension_802_53 : a k 53*normalRep k 802=normalRep k 904 := by
  change a k 53*walk k 10 [10, 11, 26, 31, 73, 67, 32, 62]=walk k 10 [10, 11, 26, 31, 73, 67, 32, 61, 35]
  rw [← walk_snoc]
  exact Universal.mul_reduced_697 (a k) (relation_zero k) (e k 10)
lemma arrow_span_802 (b : Fin 75) : a k b*normalRep k 802 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_802_52 k]
      exact normal_mem k 905
    · rw [extension_802_53 k]
      exact normal_mem k 904
  · rw [show a k b*normalRep k 802=0 from arrow_incompatible k b 10 37 [10, 11, 26, 31, 73, 67, 32, 62] (normal_endpoints 802) h]
    exact Submodule.zero_mem _
lemma extension_803_54 : a k 54*normalRep k 803=0 := by
  change a k 54*walk k 11 [11, 26, 31, 73, 67, 32, 61, 35]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_670 (a k) (relation_zero k) (e k 11)
lemma extension_803_55 : a k 55*normalRep k 803=normalRep k 906 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35] 55).symm
lemma extension_803_56 : a k 56*normalRep k 803=normalRep k 907 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 61, 35] 56).symm
lemma arrow_span_803 (b : Fin 75) : a k b*normalRep k 803 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_803_54 k]
      exact Submodule.zero_mem _
    · rw [extension_803_55 k]
      exact normal_mem k 906
    · rw [extension_803_56 k]
      exact normal_mem k 907
  · rw [show a k b*normalRep k 803=0 from arrow_incompatible k b 11 38 [11, 26, 31, 73, 67, 32, 61, 35] (normal_endpoints 803) h]
    exact Submodule.zero_mem _
lemma extension_804_41 : a k 41*normalRep k 804=normalRep k 907 := by
  change a k 41*walk k 11 [11, 26, 31, 73, 67, 32, 62, 52]=walk k 11 [11, 26, 31, 73, 67, 32, 61, 35, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_684 (a k) (relation_zero k) (e k 11)
lemma extension_804_42 : a k 42*normalRep k 804=normalRep k 908 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32, 62, 52] 42).symm
lemma arrow_span_804 (b : Fin 75) : a k b*normalRep k 804 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_804_41 k]
      exact normal_mem k 907
    · rw [extension_804_42 k]
      exact normal_mem k 908
  · rw [show a k b*normalRep k 804=0 from arrow_incompatible k b 11 31 [11, 26, 31, 73, 67, 32, 62, 52] (normal_endpoints 804) h]
    exact Submodule.zero_mem _
lemma extension_805_69 : a k 69*normalRep k 805=normalRep k 909 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49] 69).symm
lemma extension_805_70 : a k 70*normalRep k 805=0 := by
  change a k 70*walk k 12 [12, 35, 55, 27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_681 (a k) (relation_zero k) (e k 12)
lemma extension_805_71 : a k 71*normalRep k 805=normalRep k 910 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33, 13, 49] 71).symm
lemma arrow_span_805 (b : Fin 75) : a k b*normalRep k 805 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_805_69 k]
      exact normal_mem k 909
    · rw [extension_805_70 k]
      exact Submodule.zero_mem _
    · rw [extension_805_71 k]
      exact normal_mem k 910
  · rw [show a k b*normalRep k 805=0 from arrow_incompatible k b 12 43 [12, 35, 55, 27, 58, 33, 13, 49] (normal_endpoints 805) h]
    exact Submodule.zero_mem _
lemma extension_806_69 : a k 69*normalRep k 806=(-normalRep k 909) := by
  change a k 69*walk k 12 [12, 35, 55, 27, 58, 34, 63, 21]=(-walk k 12 [12, 35, 55, 27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_671 (a k) (relation_zero k) (e k 12)
lemma extension_806_70 : a k 70*normalRep k 806=normalRep k 911 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 34, 63, 21] 70).symm
lemma extension_806_71 : a k 71*normalRep k 806=0 := by
  change a k 71*walk k 12 [12, 35, 55, 27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_655 (a k) (relation_zero k) (e k 12)
lemma arrow_span_806 (b : Fin 75) : a k b*normalRep k 806 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_806_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 909)
    · rw [extension_806_70 k]
      exact normal_mem k 911
    · rw [extension_806_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 806=0 from arrow_incompatible k b 12 43 [12, 35, 55, 27, 58, 34, 63, 21] (normal_endpoints 806) h]
    exact Submodule.zero_mem _
lemma extension_807_41 : a k 41*normalRep k 807=normalRep k 912 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_807_42 : a k 42*normalRep k 807=0 := by
  change a k 42*walk k 13 [13, 49, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_642 (a k) (relation_zero k) (e k 13)
lemma arrow_span_807 (b : Fin 75) : a k b*normalRep k 807 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_807_41 k]
      exact normal_mem k 912
    · rw [extension_807_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 807=0 from arrow_incompatible k b 13 31 [13, 49, 69, 8, 66, 24, 18, 9] (normal_endpoints 807) h]
    exact Submodule.zero_mem _
lemma extension_808_54 : a k 54*normalRep k 808=normalRep k 913 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_808_55 : a k 55*normalRep k 808=0 := by
  change a k 55*walk k 13 [13, 49, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_631 (a k) (relation_zero k) (e k 13)
lemma extension_808_56 : a k 56*normalRep k 808=normalRep k 912 := by
  change a k 56*walk k 13 [13, 49, 69, 8, 66, 24, 19, 53]=walk k 13 [13, 49, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_685 (a k) (relation_zero k) (e k 13)
lemma arrow_span_808 (b : Fin 75) : a k b*normalRep k 808 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_808_54 k]
      exact normal_mem k 913
    · rw [extension_808_55 k]
      exact Submodule.zero_mem _
    · rw [extension_808_56 k]
      exact normal_mem k 912
  · rw [show a k b*normalRep k 808=0 from arrow_incompatible k b 13 38 [13, 49, 69, 8, 66, 24, 19, 53] (normal_endpoints 808) h]
    exact Submodule.zero_mem _
lemma extension_809_30 : a k 30*normalRep k 809=normalRep k 914 := by
  exact (walk_snoc k 14 [14, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_809_31 : a k 31*normalRep k 809=0 := by
  change a k 31*walk k 14 [14, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_652 (a k) (relation_zero k) (e k 14)
lemma arrow_span_809 (b : Fin 75) : a k b*normalRep k 809 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_809_30 k]
      exact normal_mem k 914
    · rw [extension_809_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 809=0 from arrow_incompatible k b 14 24 [14, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 809) h]
    exact Submodule.zero_mem _
lemma arrow_span_810 (b : Fin 75) : a k b*normalRep k 810 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 810=0 from arrow_incompatible k b 15 46 [15, 1, 34, 63, 20, 30, 2, 0] (normal_endpoints 810) h]
    exact Submodule.zero_mem _
lemma extension_811_41 : a k 41*normalRep k 811=normalRep k 915 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_811_42 : a k 42*normalRep k 811=0 := by
  change a k 42*walk k 16 [17, 21, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_629 (a k) (relation_zero k) (e k 16)
lemma arrow_span_811 (b : Fin 75) : a k b*normalRep k 811 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_811_41 k]
      exact normal_mem k 915
    · rw [extension_811_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 811=0 from arrow_incompatible k b 16 31 [17, 21, 69, 8, 66, 24, 18, 9] (normal_endpoints 811) h]
    exact Submodule.zero_mem _
lemma extension_812_54 : a k 54*normalRep k 812=normalRep k 916 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_812_55 : a k 55*normalRep k 812=0 := by
  change a k 55*walk k 16 [17, 21, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_632 (a k) (relation_zero k) (e k 16)
lemma extension_812_56 : a k 56*normalRep k 812=normalRep k 915 := by
  change a k 56*walk k 16 [17, 21, 69, 8, 66, 24, 19, 53]=walk k 16 [17, 21, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_686 (a k) (relation_zero k) (e k 16)
lemma arrow_span_812 (b : Fin 75) : a k b*normalRep k 812 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_812_54 k]
      exact normal_mem k 916
    · rw [extension_812_55 k]
      exact Submodule.zero_mem _
    · rw [extension_812_56 k]
      exact normal_mem k 915
  · rw [show a k b*normalRep k 812=0 from arrow_incompatible k b 16 38 [17, 21, 69, 8, 66, 24, 19, 53] (normal_endpoints 812) h]
    exact Submodule.zero_mem _
lemma extension_813_30 : a k 30*normalRep k 813=normalRep k 917 := by
  exact (walk_snoc k 17 [18, 9, 41, 44, 57, 5, 63, 20] 30).symm
lemma extension_813_31 : a k 31*normalRep k 813=0 := by
  change a k 31*walk k 17 [18, 9, 41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_653 (a k) (relation_zero k) (e k 17)
lemma arrow_span_813 (b : Fin 75) : a k b*normalRep k 813 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_813_30 k]
      exact normal_mem k 917
    · rw [extension_813_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 813=0 from arrow_incompatible k b 17 24 [18, 9, 41, 44, 57, 5, 63, 20] (normal_endpoints 813) h]
    exact Submodule.zero_mem _
lemma extension_814_43 : a k 43*normalRep k 814=0 := by
  change a k 43*walk k 18 [21, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_634 (a k) (relation_zero k) (e k 18)
lemma extension_814_44 : a k 44*normalRep k 814=normalRep k 918 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_814 (b : Fin 75) : a k b*normalRep k 814 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_814_43 k]
      exact Submodule.zero_mem _
    · rw [extension_814_44 k]
      exact normal_mem k 918
  · rw [show a k b*normalRep k 814=0 from arrow_incompatible k b 18 32 [21, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 814) h]
    exact Submodule.zero_mem _
lemma extension_815_15 : a k 15*normalRep k 815=normalRep k 919 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_815_16 : a k 16*normalRep k 815=normalRep k 918 := by
  change a k 16*walk k 18 [21, 69, 8, 66, 24, 19, 53, 54]=walk k 18 [21, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_688 (a k) (relation_zero k) (e k 18)
lemma arrow_span_815 (b : Fin 75) : a k b*normalRep k 815 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_815_15 k]
      exact normal_mem k 919
    · rw [extension_815_16 k]
      exact normal_mem k 918
  · rw [show a k b*normalRep k 815=0 from arrow_incompatible k b 18 15 [21, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 815) h]
    exact Submodule.zero_mem _
lemma extension_816_33 : a k 33*normalRep k 816=0 := by
  change a k 33*walk k 19 [22, 3, 40, 60, 4, 54, 15, 1]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_621 (a k) (relation_zero k) (e k 19)
lemma extension_816_34 : a k 34*normalRep k 816=normalRep k 920 := by
  exact (walk_snoc k 19 [22, 3, 40, 60, 4, 54, 15, 1] 34).symm
lemma arrow_span_816 (b : Fin 75) : a k b*normalRep k 816 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_816_33 k]
      exact Submodule.zero_mem _
    · rw [extension_816_34 k]
      exact normal_mem k 920
  · rw [show a k b*normalRep k 816=0 from arrow_incompatible k b 19 26 [22, 3, 40, 60, 4, 54, 15, 1] (normal_endpoints 816) h]
    exact Submodule.zero_mem _
lemma extension_817_5 : a k 5*normalRep k 817=normalRep k 920 := by
  change a k 5*walk k 19 [22, 3, 40, 60, 4, 54, 16, 57]=walk k 19 [22, 3, 40, 60, 4, 54, 15, 1, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_693 (a k) (relation_zero k) (e k 19)
lemma arrow_span_817 (b : Fin 75) : a k b*normalRep k 817 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_817_5 k]
      exact normal_mem k 920
  · rw [show a k b*normalRep k 817=0 from arrow_incompatible k b 19 5 [22, 3, 40, 60, 4, 54, 16, 57] (normal_endpoints 817) h]
    exact Submodule.zero_mem _
lemma extension_818_20 : a k 20*normalRep k 818=normalRep k 921 := by
  exact (walk_snoc k 20 [24, 18, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_818_21 : a k 21*normalRep k 818=0 := by
  change a k 21*walk k 20 [24, 18, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_700 (a k) (relation_zero k) (e k 20)
lemma arrow_span_818 (b : Fin 75) : a k b*normalRep k 818 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_818_20 k]
      exact normal_mem k 921
    · rw [extension_818_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 818=0 from arrow_incompatible k b 20 18 [24, 18, 9, 41, 44, 57, 5, 63] (normal_endpoints 818) h]
    exact Submodule.zero_mem _
lemma extension_819_27 : a k 27*normalRep k 819=normalRep k 922 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 55] 27).symm
lemma arrow_span_819 (b : Fin 75) : a k b*normalRep k 819 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_819_27 k]
      exact normal_mem k 922
  · rw [show a k b*normalRep k 819=0 from arrow_incompatible k b 21 22 [26, 31, 73, 67, 32, 61, 35, 55] (normal_endpoints 819) h]
    exact Submodule.zero_mem _
lemma extension_820_43 : a k 43*normalRep k 820=normalRep k 923 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61, 35, 56] 43).symm
lemma extension_820_44 : a k 44*normalRep k 820=normalRep k 922 := by
  change a k 44*walk k 21 [26, 31, 73, 67, 32, 61, 35, 56]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 55, 27]
  rw [← walk_snoc]
  exact Universal.mul_reduced_689 (a k) (relation_zero k) (e k 21)
lemma arrow_span_820 (b : Fin 75) : a k b*normalRep k 820 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_820_43 k]
      exact normal_mem k 923
    · rw [extension_820_44 k]
      exact normal_mem k 922
  · rw [show a k b*normalRep k 820=0 from arrow_incompatible k b 21 32 [26, 31, 73, 67, 32, 61, 35, 56] (normal_endpoints 820) h]
    exact Submodule.zero_mem _
lemma extension_821_45 : a k 45*normalRep k 821=normalRep k 924 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 62, 52, 42] 45).symm
lemma extension_821_46 : a k 46*normalRep k 821=normalRep k 923 := by
  change a k 46*walk k 21 [26, 31, 73, 67, 32, 62, 52, 42]=walk k 21 [26, 31, 73, 67, 32, 61, 35, 56, 43]
  rw [← walk_snoc]
  exact Universal.mul_reduced_677 (a k) (relation_zero k) (e k 21)
lemma arrow_span_821 (b : Fin 75) : a k b*normalRep k 821 ∈ normalSpan k := by
  by_cases h : arrowSource b=33
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [45, 46] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_821_45 k]
      exact normal_mem k 924
    · rw [extension_821_46 k]
      exact normal_mem k 923
  · rw [show a k b*normalRep k 821=0 from arrow_incompatible k b 21 33 [26, 31, 73, 67, 32, 62, 52, 42] (normal_endpoints 821) h]
    exact Submodule.zero_mem _
lemma extension_822_24 : a k 24*normalRep k 822=normalRep k 925 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66] 24).symm
lemma extension_822_25 : a k 25*normalRep k 822=normalRep k 926 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_822 (b : Fin 75) : a k b*normalRep k 822 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_822_24 k]
      exact normal_mem k 925
    · rw [extension_822_25 k]
      exact normal_mem k 926
  · rw [show a k b*normalRep k 822=0 from arrow_incompatible k b 22 20 [27, 58, 33, 13, 49, 69, 8, 66] (normal_endpoints 822) h]
    exact Submodule.zero_mem _
lemma extension_823_39 : a k 39*normalRep k 823=0 := by
  change a k 39*walk k 22 [27, 58, 33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_626 (a k) (relation_zero k) (e k 22)
lemma extension_823_40 : a k 40*normalRep k 823=(-normalRep k 926) := by
  change a k 40*walk k 22 [27, 58, 33, 13, 49, 69, 8, 68]=(-walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_705 (a k) (relation_zero k) (e k 22)
lemma arrow_span_823 (b : Fin 75) : a k b*normalRep k 823 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_823_39 k]
      exact Submodule.zero_mem _
    · rw [extension_823_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 926)
  · rw [show a k b*normalRep k 823=0 from arrow_incompatible k b 22 30 [27, 58, 33, 13, 49, 69, 8, 68] (normal_endpoints 823) h]
    exact Submodule.zero_mem _
lemma extension_824_28 : a k 28*normalRep k 824=normalRep k 927 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 71, 72, 38] 28).symm
lemma extension_824_29 : a k 29*normalRep k 824=normalRep k 925 := by
  change a k 29*walk k 22 [27, 58, 33, 13, 49, 71, 72, 38]=walk k 22 [27, 58, 33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_673 (a k) (relation_zero k) (e k 22)
lemma arrow_span_824 (b : Fin 75) : a k b*normalRep k 824 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_824_28 k]
      exact normal_mem k 927
    · rw [extension_824_29 k]
      exact normal_mem k 925
  · rw [show a k b*normalRep k 824=0 from arrow_incompatible k b 22 23 [27, 58, 33, 13, 49, 71, 72, 38] (normal_endpoints 824) h]
    exact Submodule.zero_mem _
lemma extension_825_20 : a k 20*normalRep k 825=normalRep k 928 := by
  exact (walk_snoc k 23 [28, 14, 9, 41, 44, 57, 5, 63] 20).symm
lemma extension_825_21 : a k 21*normalRep k 825=0 := by
  change a k 21*walk k 23 [28, 14, 9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_701 (a k) (relation_zero k) (e k 23)
lemma arrow_span_825 (b : Fin 75) : a k b*normalRep k 825 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_825_20 k]
      exact normal_mem k 928
    · rw [extension_825_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 825=0 from arrow_incompatible k b 23 18 [28, 14, 9, 41, 44, 57, 5, 63] (normal_endpoints 825) h]
    exact Submodule.zero_mem _
lemma extension_826_57 : a k 57*normalRep k 826=0 := by
  change a k 57*walk k 24 [31, 73, 67, 32, 61, 35, 55, 27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_665 (a k) (relation_zero k) (e k 24)
lemma extension_826_58 : a k 58*normalRep k 826=normalRep k 929 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27] 58).symm
lemma extension_826_59 : a k 59*normalRep k 826=normalRep k 930 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 55, 27] 59).symm
lemma arrow_span_826 (b : Fin 75) : a k b*normalRep k 826 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_826_57 k]
      exact Submodule.zero_mem _
    · rw [extension_826_58 k]
      exact normal_mem k 929
    · rw [extension_826_59 k]
      exact normal_mem k 930
  · rw [show a k b*normalRep k 826=0 from arrow_incompatible k b 24 39 [31, 73, 67, 32, 61, 35, 55, 27] (normal_endpoints 826) h]
    exact Submodule.zero_mem _
lemma extension_827_47 : a k 47*normalRep k 827=normalRep k 931 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35, 56, 43] 47).symm
lemma extension_827_48 : a k 48*normalRep k 827=normalRep k 930 := by
  change a k 48*walk k 24 [31, 73, 67, 32, 61, 35, 56, 43]=walk k 24 [31, 73, 67, 32, 61, 35, 55, 27, 59]
  rw [← walk_snoc]
  exact Universal.mul_reduced_678 (a k) (relation_zero k) (e k 24)
lemma arrow_span_827 (b : Fin 75) : a k b*normalRep k 827 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_827_47 k]
      exact normal_mem k 931
    · rw [extension_827_48 k]
      exact normal_mem k 930
  · rw [show a k b*normalRep k 827=0 from arrow_incompatible k b 24 34 [31, 73, 67, 32, 61, 35, 56, 43] (normal_endpoints 827) h]
    exact Submodule.zero_mem _
lemma extension_828_6 : a k 6*normalRep k 828=normalRep k 931 := by
  change a k 6*walk k 24 [31, 73, 67, 32, 62, 52, 42, 45]=walk k 24 [31, 73, 67, 32, 61, 35, 56, 43, 47]
  rw [← walk_snoc]
  exact Universal.mul_reduced_679 (a k) (relation_zero k) (e k 24)
lemma arrow_span_828 (b : Fin 75) : a k b*normalRep k 828 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_828_6 k]
      exact normal_mem k 931
  · rw [show a k b*normalRep k 828=0 from arrow_incompatible k b 24 6 [31, 73, 67, 32, 62, 52, 42, 45] (normal_endpoints 828) h]
    exact Submodule.zero_mem _
lemma extension_829_49 : a k 49*normalRep k 829=normalRep k 932 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 33, 13] 49).symm
lemma arrow_span_829 (b : Fin 75) : a k b*normalRep k 829 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_829_49 k]
      exact normal_mem k 932
  · rw [show a k b*normalRep k 829=0 from arrow_incompatible k b 25 35 [32, 61, 35, 55, 27, 58, 33, 13] (normal_endpoints 829) h]
    exact Submodule.zero_mem _
lemma extension_830_20 : a k 20*normalRep k 830=0 := by
  change a k 20*walk k 25 [32, 61, 35, 55, 27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_647 (a k) (relation_zero k) (e k 25)
lemma extension_830_21 : a k 21*normalRep k 830=normalRep k 933 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58, 34, 63] 21).symm
lemma arrow_span_830 (b : Fin 75) : a k b*normalRep k 830 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_830_20 k]
      exact Submodule.zero_mem _
    · rw [extension_830_21 k]
      exact normal_mem k 933
  · rw [show a k b*normalRep k 830=0 from arrow_incompatible k b 25 18 [32, 61, 35, 55, 27, 58, 34, 63] (normal_endpoints 830) h]
    exact Submodule.zero_mem _
lemma extension_831_36 : a k 36*normalRep k 831=normalRep k 933 + normalRep k 932 := by
  change a k 36*walk k 25 [32, 61, 35, 55, 27, 58, 34, 64]=walk k 25 [32, 61, 35, 55, 27, 58, 34, 63, 21] + walk k 25 [32, 61, 35, 55, 27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_702 (a k) (relation_zero k) (e k 25)
lemma arrow_span_831 (b : Fin 75) : a k b*normalRep k 831 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_831_36 k]
      exact (normalSpan k).add_mem (normal_mem k 933) (normal_mem k 932)
  · rw [show a k b*normalRep k 831=0 from arrow_incompatible k b 25 28 [32, 61, 35, 55, 27, 58, 34, 64] (normal_endpoints 831) h]
    exact Submodule.zero_mem _
lemma extension_832_9 : a k 9*normalRep k 832=normalRep k 934 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_832 (b : Fin 75) : a k b*normalRep k 832 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_832_9 k]
      exact normal_mem k 934
  · rw [show a k b*normalRep k 832=0 from arrow_incompatible k b 26 9 [33, 13, 49, 69, 8, 66, 24, 18] (normal_endpoints 832) h]
    exact Submodule.zero_mem _
lemma extension_833_52 : a k 52*normalRep k 833=normalRep k 934 := by
  change a k 52*walk k 26 [33, 13, 49, 69, 8, 66, 24, 19]=walk k 26 [33, 13, 49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_650 (a k) (relation_zero k) (e k 26)
lemma extension_833_53 : a k 53*normalRep k 833=normalRep k 935 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_833 (b : Fin 75) : a k b*normalRep k 833 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_833_52 k]
      exact normal_mem k 934
    · rw [extension_833_53 k]
      exact normal_mem k 935
  · rw [show a k b*normalRep k 833=0 from arrow_incompatible k b 26 37 [33, 13, 49, 69, 8, 66, 24, 19] (normal_endpoints 833) h]
    exact Submodule.zero_mem _
lemma extension_834_4 : a k 4*normalRep k 834=normalRep k 935 := by
  change a k 4*walk k 26 [33, 13, 49, 69, 8, 66, 25, 60]=walk k 26 [33, 13, 49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_698 (a k) (relation_zero k) (e k 26)
lemma arrow_span_834 (b : Fin 75) : a k b*normalRep k 834 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_834_4 k]
      exact normal_mem k 935
  · rw [show a k b*normalRep k 834=0 from arrow_incompatible k b 26 4 [33, 13, 49, 69, 8, 66, 25, 60] (normal_endpoints 834) h]
    exact Submodule.zero_mem _
lemma extension_835_8 : a k 8*normalRep k 835=normalRep k 936 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_835 (b : Fin 75) : a k b*normalRep k 835 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_835_8 k]
      exact normal_mem k 936
  · rw [show a k b*normalRep k 835=0 from arrow_incompatible k b 27 8 [35, 55, 27, 58, 33, 13, 49, 69] (normal_endpoints 835) h]
    exact Submodule.zero_mem _
lemma extension_836_72 : a k 72*normalRep k 836=normalRep k 937 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13, 49, 71] 72).symm
lemma extension_836_73 : a k 73*normalRep k 836=normalRep k 936 := by
  change a k 73*walk k 27 [35, 55, 27, 58, 33, 13, 49, 71]=walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_708 (a k) (relation_zero k) (e k 27)
lemma arrow_span_836 (b : Fin 75) : a k b*normalRep k 836 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_836_72 k]
      exact normal_mem k 937
    · rw [extension_836_73 k]
      exact normal_mem k 936
  · rw [show a k b*normalRep k 836=0 from arrow_incompatible k b 27 44 [35, 55, 27, 58, 33, 13, 49, 71] (normal_endpoints 836) h]
    exact Submodule.zero_mem _
lemma extension_837_22 : a k 22*normalRep k 837=normalRep k 938 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 34, 63, 21, 70] 22).symm
lemma extension_837_23 : a k 23*normalRep k 837=normalRep k 936 := by
  change a k 23*walk k 27 [35, 55, 27, 58, 34, 63, 21, 70]=walk k 27 [35, 55, 27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_709 (a k) (relation_zero k) (e k 27)
lemma arrow_span_837 (b : Fin 75) : a k b*normalRep k 837 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_837_22 k]
      exact normal_mem k 938
    · rw [extension_837_23 k]
      exact normal_mem k 936
  · rw [show a k b*normalRep k 837=0 from arrow_incompatible k b 27 19 [35, 55, 27, 58, 34, 63, 21, 70] (normal_endpoints 837) h]
    exact Submodule.zero_mem _
lemma extension_838_15 : a k 15*normalRep k 838=normalRep k 939 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 60, 4, 54] 15).symm
lemma extension_838_16 : a k 16*normalRep k 838=normalRep k 940 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 60, 4, 54] 16).symm
lemma arrow_span_838 (b : Fin 75) : a k b*normalRep k 838 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_838_15 k]
      exact normal_mem k 939
    · rw [extension_838_16 k]
      exact normal_mem k 940
  · rw [show a k b*normalRep k 838=0 from arrow_incompatible k b 28 15 [36, 70, 22, 3, 40, 60, 4, 54] (normal_endpoints 838) h]
    exact Submodule.zero_mem _
lemma extension_839_43 : a k 43*normalRep k 839=0 := by
  change a k 43*walk k 28 [36, 70, 22, 3, 40, 60, 4, 56]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_635 (a k) (relation_zero k) (e k 28)
lemma extension_839_44 : a k 44*normalRep k 839=normalRep k 940 := by
  change a k 44*walk k 28 [36, 70, 22, 3, 40, 60, 4, 56]=walk k 28 [36, 70, 22, 3, 40, 60, 4, 54, 16]
  rw [← walk_snoc]
  exact Universal.mul_reduced_690 (a k) (relation_zero k) (e k 28)
lemma arrow_span_839 (b : Fin 75) : a k b*normalRep k 839 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_839_43 k]
      exact Submodule.zero_mem _
    · rw [extension_839_44 k]
      exact normal_mem k 940
  · rw [show a k b*normalRep k 839=0 from arrow_incompatible k b 28 32 [36, 70, 22, 3, 40, 60, 4, 56] (normal_endpoints 839) h]
    exact Submodule.zero_mem _
lemma extension_840_63 : a k 63*normalRep k 840=normalRep k 941 := by
  exact (walk_snoc k 29 [37, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_840_64 : a k 64*normalRep k 840=0 := by
  change a k 64*walk k 29 [37, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_624 (a k) (relation_zero k) (e k 29)
lemma extension_840_65 : a k 65*normalRep k 840=0 := by
  change a k 65*walk k 29 [37, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_638 (a k) (relation_zero k) (e k 29)
lemma arrow_span_840 (b : Fin 75) : a k b*normalRep k 840 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_840_63 k]
      exact normal_mem k 941
    · rw [extension_840_64 k]
      exact Submodule.zero_mem _
    · rw [extension_840_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 840=0 from arrow_incompatible k b 29 41 [37, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 840) h]
    exact Submodule.zero_mem _
lemma extension_841_49 : a k 49*normalRep k 841=normalRep k 942 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 33, 13] 49).symm
lemma arrow_span_841 (b : Fin 75) : a k b*normalRep k 841 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_841_49 k]
      exact normal_mem k 942
  · rw [show a k b*normalRep k 841=0 from arrow_incompatible k b 30 35 [39, 12, 35, 55, 27, 58, 33, 13] (normal_endpoints 841) h]
    exact Submodule.zero_mem _
lemma extension_842_20 : a k 20*normalRep k 842=0 := by
  change a k 20*walk k 30 [39, 12, 35, 55, 27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_648 (a k) (relation_zero k) (e k 30)
lemma extension_842_21 : a k 21*normalRep k 842=normalRep k 943 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58, 34, 63] 21).symm
lemma arrow_span_842 (b : Fin 75) : a k b*normalRep k 842 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_842_20 k]
      exact Submodule.zero_mem _
    · rw [extension_842_21 k]
      exact normal_mem k 943
  · rw [show a k b*normalRep k 842=0 from arrow_incompatible k b 30 18 [39, 12, 35, 55, 27, 58, 34, 63] (normal_endpoints 842) h]
    exact Submodule.zero_mem _
lemma extension_843_36 : a k 36*normalRep k 843=normalRep k 943 + normalRep k 942 := by
  change a k 36*walk k 30 [39, 12, 35, 55, 27, 58, 34, 64]=walk k 30 [39, 12, 35, 55, 27, 58, 34, 63, 21] + walk k 30 [39, 12, 35, 55, 27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_703 (a k) (relation_zero k) (e k 30)
lemma arrow_span_843 (b : Fin 75) : a k b*normalRep k 843 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_843_36 k]
      exact (normalSpan k).add_mem (normal_mem k 943) (normal_mem k 942)
  · rw [show a k b*normalRep k 843=0 from arrow_incompatible k b 30 28 [39, 12, 35, 55, 27, 58, 34, 64] (normal_endpoints 843) h]
    exact Submodule.zero_mem _
lemma extension_844_20 : a k 20*normalRep k 844=normalRep k 944 := by
  exact (walk_snoc k 30 [40, 60, 4, 54, 15, 1, 34, 63] 20).symm
lemma extension_844_21 : a k 21*normalRep k 844=0 := by
  change a k 21*walk k 30 [40, 60, 4, 54, 15, 1, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_704 (a k) (relation_zero k) (e k 30)
lemma arrow_span_844 (b : Fin 75) : a k b*normalRep k 844 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_844_20 k]
      exact normal_mem k 944
    · rw [extension_844_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 844=0 from arrow_incompatible k b 30 18 [40, 60, 4, 54, 15, 1, 34, 63] (normal_endpoints 844) h]
    exact Submodule.zero_mem _
lemma extension_845_66 : a k 66*normalRep k 845=normalRep k 945 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8] 66).symm
lemma extension_845_67 : a k 67*normalRep k 845=0 := by
  change a k 67*walk k 31 [41, 43, 47, 7, 17, 21, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_640 (a k) (relation_zero k) (e k 31)
lemma extension_845_68 : a k 68*normalRep k 845=normalRep k 946 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21, 69, 8] 68).symm
lemma arrow_span_845 (b : Fin 75) : a k b*normalRep k 845 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_845_66 k]
      exact normal_mem k 945
    · rw [extension_845_67 k]
      exact Submodule.zero_mem _
    · rw [extension_845_68 k]
      exact normal_mem k 946
  · rw [show a k b*normalRep k 845=0 from arrow_incompatible k b 31 42 [41, 43, 47, 7, 17, 21, 69, 8] (normal_endpoints 845) h]
    exact Submodule.zero_mem _
lemma extension_846_3 : a k 3*normalRep k 846=normalRep k 946 := by
  change a k 3*walk k 31 [41, 43, 47, 7, 17, 21, 70, 22]=walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 68]
  rw [← walk_snoc]
  exact Universal.mul_reduced_657 (a k) (relation_zero k) (e k 31)
lemma arrow_span_846 (b : Fin 75) : a k b*normalRep k 846 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_846_3 k]
      exact normal_mem k 946
  · rw [show a k b*normalRep k 846=0 from arrow_incompatible k b 31 3 [41, 43, 47, 7, 17, 21, 70, 22] (normal_endpoints 846) h]
    exact Submodule.zero_mem _
lemma extension_847_37 : a k 37*normalRep k 847=(-normalRep k 945) := by
  change a k 37*walk k 31 [41, 43, 48, 51, 64, 36, 71, 72]=(-walk k 31 [41, 43, 47, 7, 17, 21, 69, 8, 66])
  rw [← walk_snoc]
  exact Universal.mul_reduced_712 (a k) (relation_zero k) (e k 31)
lemma extension_847_38 : a k 38*normalRep k 847=normalRep k 947 := by
  exact (walk_snoc k 31 [41, 43, 48, 51, 64, 36, 71, 72] 38).symm
lemma arrow_span_847 (b : Fin 75) : a k b*normalRep k 847 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_847_37 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 945)
    · rw [extension_847_38 k]
      exact normal_mem k 947
  · rw [show a k b*normalRep k 847=0 from arrow_incompatible k b 31 29 [41, 43, 48, 51, 64, 36, 71, 72] (normal_endpoints 847) h]
    exact Submodule.zero_mem _
lemma extension_848_0 : a k 0*normalRep k 848=normalRep k 948 := by
  exact (walk_snoc k 31 [41, 44, 57, 5, 63, 20, 30, 2] 0).symm
lemma arrow_span_848 (b : Fin 75) : a k b*normalRep k 848 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_848_0 k]
      exact normal_mem k 948
  · rw [show a k b*normalRep k 848=0 from arrow_incompatible k b 31 0 [41, 44, 57, 5, 63, 20, 30, 2] (normal_endpoints 848) h]
    exact Submodule.zero_mem _
lemma extension_849_24 : a k 24*normalRep k 849=normalRep k 949 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66] 24).symm
lemma extension_849_25 : a k 25*normalRep k 849=normalRep k 950 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69, 8, 66] 25).symm
lemma arrow_span_849 (b : Fin 75) : a k b*normalRep k 849 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_849_24 k]
      exact normal_mem k 949
    · rw [extension_849_25 k]
      exact normal_mem k 950
  · rw [show a k b*normalRep k 849=0 from arrow_incompatible k b 32 20 [43, 47, 7, 17, 21, 69, 8, 66] (normal_endpoints 849) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
