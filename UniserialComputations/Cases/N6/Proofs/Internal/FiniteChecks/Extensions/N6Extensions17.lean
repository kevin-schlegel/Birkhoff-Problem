import N6NormalData
import N6Reduced10
import N6Reduced11
import N6Reduced12
import N6Reduced13
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_850_39 : a k 39*normalRep k 850=0 := by
  change a k 39*walk k 32 [43, 47, 7, 17, 21, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_627 (a k) (relation_zero k) (e k 32)
lemma extension_850_40 : a k 40*normalRep k 850=(-normalRep k 950) := by
  change a k 40*walk k 32 [43, 47, 7, 17, 21, 69, 8, 68]=(-walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_706 (a k) (relation_zero k) (e k 32)
lemma arrow_span_850 (b : Fin 75) : a k b*normalRep k 850 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_850_39 k]
      exact Submodule.zero_mem _
    · rw [extension_850_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 950)
  · rw [show a k b*normalRep k 850=0 from arrow_incompatible k b 32 30 [43, 47, 7, 17, 21, 69, 8, 68] (normal_endpoints 850) h]
    exact Submodule.zero_mem _
lemma extension_851_28 : a k 28*normalRep k 851=normalRep k 951 := by
  exact (walk_snoc k 32 [43, 48, 51, 64, 36, 71, 72, 38] 28).symm
lemma extension_851_29 : a k 29*normalRep k 851=(-normalRep k 949) := by
  change a k 29*walk k 32 [43, 48, 51, 64, 36, 71, 72, 38]=(-walk k 32 [43, 47, 7, 17, 21, 69, 8, 66, 24])
  rw [← walk_snoc]
  exact Universal.mul_reduced_674 (a k) (relation_zero k) (e k 32)
lemma arrow_span_851 (b : Fin 75) : a k b*normalRep k 851 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_851_28 k]
      exact normal_mem k 951
    · rw [extension_851_29 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 949)
  · rw [show a k b*normalRep k 851=0 from arrow_incompatible k b 32 23 [43, 48, 51, 64, 36, 71, 72, 38] (normal_endpoints 851) h]
    exact Submodule.zero_mem _
lemma arrow_span_852 (b : Fin 75) : a k b*normalRep k 852 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 852=0 from arrow_incompatible k b 32 46 [44, 57, 5, 63, 20, 30, 2, 0] (normal_endpoints 852) h]
    exact Submodule.zero_mem _
lemma extension_853_24 : a k 24*normalRep k 853=normalRep k 952 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66] 24).symm
lemma extension_853_25 : a k 25*normalRep k 853=normalRep k 953 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69, 8, 66] 25).symm
lemma arrow_span_853 (b : Fin 75) : a k b*normalRep k 853 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_853_24 k]
      exact normal_mem k 952
    · rw [extension_853_25 k]
      exact normal_mem k 953
  · rw [show a k b*normalRep k 853=0 from arrow_incompatible k b 33 20 [45, 6, 7, 17, 21, 69, 8, 66] (normal_endpoints 853) h]
    exact Submodule.zero_mem _
lemma extension_854_39 : a k 39*normalRep k 854=0 := by
  change a k 39*walk k 33 [45, 6, 7, 17, 21, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_628 (a k) (relation_zero k) (e k 33)
lemma extension_854_40 : a k 40*normalRep k 854=(-normalRep k 953) := by
  change a k 40*walk k 33 [45, 6, 7, 17, 21, 69, 8, 68]=(-walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_707 (a k) (relation_zero k) (e k 33)
lemma arrow_span_854 (b : Fin 75) : a k b*normalRep k 854 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_854_39 k]
      exact Submodule.zero_mem _
    · rw [extension_854_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 953)
  · rw [show a k b*normalRep k 854=0 from arrow_incompatible k b 33 30 [45, 6, 7, 17, 21, 69, 8, 68] (normal_endpoints 854) h]
    exact Submodule.zero_mem _
lemma extension_855_28 : a k 28*normalRep k 855=normalRep k 954 := by
  exact (walk_snoc k 33 [46, 48, 51, 64, 36, 71, 72, 38] 28).symm
lemma extension_855_29 : a k 29*normalRep k 855=(-normalRep k 952) := by
  change a k 29*walk k 33 [46, 48, 51, 64, 36, 71, 72, 38]=(-walk k 33 [45, 6, 7, 17, 21, 69, 8, 66, 24])
  rw [← walk_snoc]
  exact Universal.mul_reduced_675 (a k) (relation_zero k) (e k 33)
lemma arrow_span_855 (b : Fin 75) : a k b*normalRep k 855 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_855_28 k]
      exact normal_mem k 954
    · rw [extension_855_29 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 952)
  · rw [show a k b*normalRep k 855=0 from arrow_incompatible k b 33 23 [46, 48, 51, 64, 36, 71, 72, 38] (normal_endpoints 855) h]
    exact Submodule.zero_mem _
lemma extension_856_18 : a k 18*normalRep k 856=normalRep k 955 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24] 18).symm
lemma extension_856_19 : a k 19*normalRep k 856=normalRep k 956 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 24] 19).symm
lemma arrow_span_856 (b : Fin 75) : a k b*normalRep k 856 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_856_18 k]
      exact normal_mem k 955
    · rw [extension_856_19 k]
      exact normal_mem k 956
  · rw [show a k b*normalRep k 856=0 from arrow_incompatible k b 34 17 [47, 7, 17, 21, 69, 8, 66, 24] (normal_endpoints 856) h]
    exact Submodule.zero_mem _
lemma extension_857_60 : a k 60*normalRep k 857=normalRep k 957 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8, 66, 25] 60).symm
lemma extension_857_61 : a k 61*normalRep k 857=0 := by
  change a k 61*walk k 34 [47, 7, 17, 21, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_660 (a k) (relation_zero k) (e k 34)
lemma extension_857_62 : a k 62*normalRep k 857=normalRep k 956 := by
  change a k 62*walk k 34 [47, 7, 17, 21, 69, 8, 66, 25]=walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_663 (a k) (relation_zero k) (e k 34)
lemma arrow_span_857 (b : Fin 75) : a k b*normalRep k 857 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_857_60 k]
      exact normal_mem k 957
    · rw [extension_857_61 k]
      exact Submodule.zero_mem _
    · rw [extension_857_62 k]
      exact normal_mem k 956
  · rw [show a k b*normalRep k 857=0 from arrow_incompatible k b 34 40 [47, 7, 17, 21, 69, 8, 66, 25] (normal_endpoints 857) h]
    exact Submodule.zero_mem _
lemma extension_858_14 : a k 14*normalRep k 858=(-normalRep k 955) := by
  change a k 14*walk k 34 [48, 51, 64, 36, 71, 72, 38, 28]=(-walk k 34 [47, 7, 17, 21, 69, 8, 66, 24, 18])
  rw [← walk_snoc]
  exact Universal.mul_reduced_666 (a k) (relation_zero k) (e k 34)
lemma arrow_span_858 (b : Fin 75) : a k b*normalRep k 858 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_858_14 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 955)
  · rw [show a k b*normalRep k 858=0 from arrow_incompatible k b 34 14 [48, 51, 64, 36, 71, 72, 38, 28] (normal_endpoints 858) h]
    exact Submodule.zero_mem _
lemma extension_859_43 : a k 43*normalRep k 859=0 := by
  change a k 43*walk k 35 [49, 69, 8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_636 (a k) (relation_zero k) (e k 35)
lemma extension_859_44 : a k 44*normalRep k 859=normalRep k 958 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_859 (b : Fin 75) : a k b*normalRep k 859 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_859_43 k]
      exact Submodule.zero_mem _
    · rw [extension_859_44 k]
      exact normal_mem k 958
  · rw [show a k b*normalRep k 859=0 from arrow_incompatible k b 35 32 [49, 69, 8, 66, 24, 18, 9, 41] (normal_endpoints 859) h]
    exact Submodule.zero_mem _
lemma extension_860_15 : a k 15*normalRep k 860=normalRep k 959 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 19, 53, 54] 15).symm
lemma extension_860_16 : a k 16*normalRep k 860=normalRep k 958 := by
  change a k 16*walk k 35 [49, 69, 8, 66, 24, 19, 53, 54]=walk k 35 [49, 69, 8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_691 (a k) (relation_zero k) (e k 35)
lemma arrow_span_860 (b : Fin 75) : a k b*normalRep k 860 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_860_15 k]
      exact normal_mem k 959
    · rw [extension_860_16 k]
      exact normal_mem k 958
  · rw [show a k b*normalRep k 860=0 from arrow_incompatible k b 35 15 [49, 69, 8, 66, 24, 19, 53, 54] (normal_endpoints 860) h]
    exact Submodule.zero_mem _
lemma extension_861_9 : a k 9*normalRep k 861=normalRep k 960 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_861 (b : Fin 75) : a k b*normalRep k 861 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_861_9 k]
      exact normal_mem k 960
  · rw [show a k b*normalRep k 861=0 from arrow_incompatible k b 36 9 [50, 17, 21, 69, 8, 66, 24, 18] (normal_endpoints 861) h]
    exact Submodule.zero_mem _
lemma extension_862_52 : a k 52*normalRep k 862=normalRep k 960 := by
  change a k 52*walk k 36 [50, 17, 21, 69, 8, 66, 24, 19]=walk k 36 [50, 17, 21, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_651 (a k) (relation_zero k) (e k 36)
lemma extension_862_53 : a k 53*normalRep k 862=normalRep k 961 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_862 (b : Fin 75) : a k b*normalRep k 862 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_862_52 k]
      exact normal_mem k 960
    · rw [extension_862_53 k]
      exact normal_mem k 961
  · rw [show a k b*normalRep k 862=0 from arrow_incompatible k b 36 37 [50, 17, 21, 69, 8, 66, 24, 19] (normal_endpoints 862) h]
    exact Submodule.zero_mem _
lemma extension_863_4 : a k 4*normalRep k 863=normalRep k 961 := by
  change a k 4*walk k 36 [50, 17, 21, 69, 8, 66, 25, 60]=walk k 36 [50, 17, 21, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_699 (a k) (relation_zero k) (e k 36)
lemma arrow_span_863 (b : Fin 75) : a k b*normalRep k 863 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_863_4 k]
      exact normal_mem k 961
  · rw [show a k b*normalRep k 863=0 from arrow_incompatible k b 36 4 [50, 17, 21, 69, 8, 66, 25, 60] (normal_endpoints 863) h]
    exact Submodule.zero_mem _
lemma extension_864_8 : a k 8*normalRep k 864=normalRep k 962 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 69] 8).symm
lemma arrow_span_864 (b : Fin 75) : a k b*normalRep k 864 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_864_8 k]
      exact normal_mem k 962
  · rw [show a k b*normalRep k 864=0 from arrow_incompatible k b 37 8 [52, 41, 43, 47, 7, 17, 21, 69] (normal_endpoints 864) h]
    exact Submodule.zero_mem _
lemma extension_865_22 : a k 22*normalRep k 865=normalRep k 963 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17, 21, 70] 22).symm
lemma extension_865_23 : a k 23*normalRep k 865=(-normalRep k 962) := by
  change a k 23*walk k 37 [52, 41, 43, 47, 7, 17, 21, 70]=(-walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_710 (a k) (relation_zero k) (e k 37)
lemma arrow_span_865 (b : Fin 75) : a k b*normalRep k 865 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_865_22 k]
      exact normal_mem k 963
    · rw [extension_865_23 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 962)
  · rw [show a k b*normalRep k 865=0 from arrow_incompatible k b 37 19 [52, 41, 43, 47, 7, 17, 21, 70] (normal_endpoints 865) h]
    exact Submodule.zero_mem _
lemma extension_866_72 : a k 72*normalRep k 866=normalRep k 964 := by
  exact (walk_snoc k 37 [52, 41, 43, 48, 51, 64, 36, 71] 72).symm
lemma extension_866_73 : a k 73*normalRep k 866=(-normalRep k 962) := by
  change a k 73*walk k 37 [52, 41, 43, 48, 51, 64, 36, 71]=(-walk k 37 [52, 41, 43, 47, 7, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_711 (a k) (relation_zero k) (e k 37)
lemma arrow_span_866 (b : Fin 75) : a k b*normalRep k 866 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_866_72 k]
      exact normal_mem k 964
    · rw [extension_866_73 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 962)
  · rw [show a k b*normalRep k 866=0 from arrow_incompatible k b 37 44 [52, 41, 43, 48, 51, 64, 36, 71] (normal_endpoints 866) h]
    exact Submodule.zero_mem _
lemma extension_867_2 : a k 2*normalRep k 867=normalRep k 965 := by
  exact (walk_snoc k 37 [52, 41, 44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_867 (b : Fin 75) : a k b*normalRep k 867 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_867_2 k]
      exact normal_mem k 965
  · rw [show a k b*normalRep k 867=0 from arrow_incompatible k b 37 2 [52, 41, 44, 57, 5, 63, 20, 30] (normal_endpoints 867) h]
    exact Submodule.zero_mem _
lemma extension_868_0 : a k 0*normalRep k 868=normalRep k 966 := by
  exact (walk_snoc k 38 [54, 15, 1, 34, 63, 20, 30, 2] 0).symm
lemma arrow_span_868 (b : Fin 75) : a k b*normalRep k 868 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_868_0 k]
      exact normal_mem k 966
  · rw [show a k b*normalRep k 868=0 from arrow_incompatible k b 38 0 [54, 15, 1, 34, 63, 20, 30, 2] (normal_endpoints 868) h]
    exact Submodule.zero_mem _
lemma extension_869_66 : a k 66*normalRep k 869=normalRep k 967 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8] 66).symm
lemma extension_869_67 : a k 67*normalRep k 869=0 := by
  change a k 67*walk k 38 [55, 27, 58, 33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_641 (a k) (relation_zero k) (e k 38)
lemma extension_869_68 : a k 68*normalRep k 869=normalRep k 968 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 69, 8] 68).symm
lemma arrow_span_869 (b : Fin 75) : a k b*normalRep k 869 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_869_66 k]
      exact normal_mem k 967
    · rw [extension_869_67 k]
      exact Submodule.zero_mem _
    · rw [extension_869_68 k]
      exact normal_mem k 968
  · rw [show a k b*normalRep k 869=0 from arrow_incompatible k b 38 42 [55, 27, 58, 33, 13, 49, 69, 8] (normal_endpoints 869) h]
    exact Submodule.zero_mem _
lemma extension_870_37 : a k 37*normalRep k 870=normalRep k 967 := by
  change a k 37*walk k 38 [55, 27, 58, 33, 13, 49, 71, 72]=walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_713 (a k) (relation_zero k) (e k 38)
lemma extension_870_38 : a k 38*normalRep k 870=normalRep k 969 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13, 49, 71, 72] 38).symm
lemma arrow_span_870 (b : Fin 75) : a k b*normalRep k 870 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_870_37 k]
      exact normal_mem k 967
    · rw [extension_870_38 k]
      exact normal_mem k 969
  · rw [show a k b*normalRep k 870=0 from arrow_incompatible k b 38 29 [55, 27, 58, 33, 13, 49, 71, 72] (normal_endpoints 870) h]
    exact Submodule.zero_mem _
lemma extension_871_3 : a k 3*normalRep k 871=(-normalRep k 968) := by
  change a k 3*walk k 38 [55, 27, 58, 34, 63, 21, 70, 22]=(-walk k 38 [55, 27, 58, 33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_658 (a k) (relation_zero k) (e k 38)
lemma arrow_span_871 (b : Fin 75) : a k b*normalRep k 871 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_871_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 968)
  · rw [show a k b*normalRep k 871=0 from arrow_incompatible k b 38 3 [55, 27, 58, 34, 63, 21, 70, 22] (normal_endpoints 871) h]
    exact Submodule.zero_mem _
lemma extension_872_18 : a k 18*normalRep k 872=normalRep k 970 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24] 18).symm
lemma extension_872_19 : a k 19*normalRep k 872=normalRep k 971 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_872 (b : Fin 75) : a k b*normalRep k 872 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_872_18 k]
      exact normal_mem k 970
    · rw [extension_872_19 k]
      exact normal_mem k 971
  · rw [show a k b*normalRep k 872=0 from arrow_incompatible k b 39 17 [58, 33, 13, 49, 69, 8, 66, 24] (normal_endpoints 872) h]
    exact Submodule.zero_mem _
lemma extension_873_60 : a k 60*normalRep k 873=normalRep k 972 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69, 8, 66, 25] 60).symm
lemma extension_873_61 : a k 61*normalRep k 873=0 := by
  change a k 61*walk k 39 [58, 33, 13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_661 (a k) (relation_zero k) (e k 39)
lemma extension_873_62 : a k 62*normalRep k 873=normalRep k 971 := by
  change a k 62*walk k 39 [58, 33, 13, 49, 69, 8, 66, 25]=walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_664 (a k) (relation_zero k) (e k 39)
lemma arrow_span_873 (b : Fin 75) : a k b*normalRep k 873 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_873_60 k]
      exact normal_mem k 972
    · rw [extension_873_61 k]
      exact Submodule.zero_mem _
    · rw [extension_873_62 k]
      exact normal_mem k 971
  · rw [show a k b*normalRep k 873=0 from arrow_incompatible k b 39 40 [58, 33, 13, 49, 69, 8, 66, 25] (normal_endpoints 873) h]
    exact Submodule.zero_mem _
lemma extension_874_14 : a k 14*normalRep k 874=normalRep k 970 := by
  change a k 14*walk k 39 [58, 33, 13, 49, 71, 72, 38, 28]=walk k 39 [58, 33, 13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_667 (a k) (relation_zero k) (e k 39)
lemma arrow_span_874 (b : Fin 75) : a k b*normalRep k 874 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_874_14 k]
      exact normal_mem k 970
  · rw [show a k b*normalRep k 874=0 from arrow_incompatible k b 39 14 [58, 33, 13, 49, 71, 72, 38, 28] (normal_endpoints 874) h]
    exact Submodule.zero_mem _
lemma extension_875_30 : a k 30*normalRep k 875=normalRep k 973 := by
  exact (walk_snoc k 40 [60, 4, 54, 15, 1, 34, 63, 20] 30).symm
lemma extension_875_31 : a k 31*normalRep k 875=0 := by
  change a k 31*walk k 40 [60, 4, 54, 15, 1, 34, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_654 (a k) (relation_zero k) (e k 40)
lemma arrow_span_875 (b : Fin 75) : a k b*normalRep k 875 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_875_30 k]
      exact normal_mem k 973
    · rw [extension_875_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 875=0 from arrow_incompatible k b 40 24 [60, 4, 54, 15, 1, 34, 63, 20] (normal_endpoints 875) h]
    exact Submodule.zero_mem _
lemma extension_876_69 : a k 69*normalRep k 876=normalRep k 974 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49] 69).symm
lemma extension_876_70 : a k 70*normalRep k 876=0 := by
  change a k 70*walk k 40 [61, 35, 55, 27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_682 (a k) (relation_zero k) (e k 40)
lemma extension_876_71 : a k 71*normalRep k 876=normalRep k 975 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 33, 13, 49] 71).symm
lemma arrow_span_876 (b : Fin 75) : a k b*normalRep k 876 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_876_69 k]
      exact normal_mem k 974
    · rw [extension_876_70 k]
      exact Submodule.zero_mem _
    · rw [extension_876_71 k]
      exact normal_mem k 975
  · rw [show a k b*normalRep k 876=0 from arrow_incompatible k b 40 43 [61, 35, 55, 27, 58, 33, 13, 49] (normal_endpoints 876) h]
    exact Submodule.zero_mem _
lemma extension_877_69 : a k 69*normalRep k 877=(-normalRep k 974) := by
  change a k 69*walk k 40 [61, 35, 55, 27, 58, 34, 63, 21]=(-walk k 40 [61, 35, 55, 27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_672 (a k) (relation_zero k) (e k 40)
lemma extension_877_70 : a k 70*normalRep k 877=normalRep k 976 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58, 34, 63, 21] 70).symm
lemma extension_877_71 : a k 71*normalRep k 877=0 := by
  change a k 71*walk k 40 [61, 35, 55, 27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_656 (a k) (relation_zero k) (e k 40)
lemma arrow_span_877 (b : Fin 75) : a k b*normalRep k 877 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_877_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 974)
    · rw [extension_877_70 k]
      exact normal_mem k 976
    · rw [extension_877_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 877=0 from arrow_incompatible k b 40 43 [61, 35, 55, 27, 58, 34, 63, 21] (normal_endpoints 877) h]
    exact Submodule.zero_mem _
lemma extension_878_41 : a k 41*normalRep k 878=normalRep k 977 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 18, 9] 41).symm
lemma extension_878_42 : a k 42*normalRep k 878=0 := by
  change a k 42*walk k 41 [63, 21, 69, 8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_630 (a k) (relation_zero k) (e k 41)
lemma arrow_span_878 (b : Fin 75) : a k b*normalRep k 878 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_878_41 k]
      exact normal_mem k 977
    · rw [extension_878_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 878=0 from arrow_incompatible k b 41 31 [63, 21, 69, 8, 66, 24, 18, 9] (normal_endpoints 878) h]
    exact Submodule.zero_mem _
lemma extension_879_54 : a k 54*normalRep k 879=normalRep k 978 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66, 24, 19, 53] 54).symm
lemma extension_879_55 : a k 55*normalRep k 879=0 := by
  change a k 55*walk k 41 [63, 21, 69, 8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_633 (a k) (relation_zero k) (e k 41)
lemma extension_879_56 : a k 56*normalRep k 879=normalRep k 977 := by
  change a k 56*walk k 41 [63, 21, 69, 8, 66, 24, 19, 53]=walk k 41 [63, 21, 69, 8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_687 (a k) (relation_zero k) (e k 41)
lemma arrow_span_879 (b : Fin 75) : a k b*normalRep k 879 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_879_54 k]
      exact normal_mem k 978
    · rw [extension_879_55 k]
      exact Submodule.zero_mem _
    · rw [extension_879_56 k]
      exact normal_mem k 977
  · rw [show a k b*normalRep k 879=0 from arrow_incompatible k b 41 38 [63, 21, 69, 8, 66, 24, 19, 53] (normal_endpoints 879) h]
    exact Submodule.zero_mem _
lemma extension_880_63 : a k 63*normalRep k 880=normalRep k 979 := by
  exact (walk_snoc k 42 [66, 24, 18, 9, 41, 44, 57, 5] 63).symm
lemma extension_880_64 : a k 64*normalRep k 880=0 := by
  change a k 64*walk k 42 [66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_625 (a k) (relation_zero k) (e k 42)
lemma extension_880_65 : a k 65*normalRep k 880=0 := by
  change a k 65*walk k 42 [66, 24, 18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_639 (a k) (relation_zero k) (e k 42)
lemma arrow_span_880 (b : Fin 75) : a k b*normalRep k 880 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_880_63 k]
      exact normal_mem k 979
    · rw [extension_880_64 k]
      exact Submodule.zero_mem _
    · rw [extension_880_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 880=0 from arrow_incompatible k b 42 41 [66, 24, 18, 9, 41, 44, 57, 5] (normal_endpoints 880) h]
    exact Submodule.zero_mem _
lemma extension_881_13 : a k 13*normalRep k 881=normalRep k 980 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 33] 13).symm
lemma arrow_span_881 (b : Fin 75) : a k b*normalRep k 881 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_881_13 k]
      exact normal_mem k 980
  · rw [show a k b*normalRep k 881=0 from arrow_incompatible k b 42 13 [67, 32, 61, 35, 55, 27, 58, 33] (normal_endpoints 881) h]
    exact Submodule.zero_mem _
lemma extension_882_63 : a k 63*normalRep k 882=normalRep k 981 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 34] 63).symm
lemma extension_882_64 : a k 64*normalRep k 882=normalRep k 982 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55, 27, 58, 34] 64).symm
lemma extension_882_65 : a k 65*normalRep k 882=normalRep k 980 := by
  change a k 65*walk k 42 [67, 32, 61, 35, 55, 27, 58, 34]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_669 (a k) (relation_zero k) (e k 42)
lemma arrow_span_882 (b : Fin 75) : a k b*normalRep k 882 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_882_63 k]
      exact normal_mem k 981
    · rw [extension_882_64 k]
      exact normal_mem k 982
    · rw [extension_882_65 k]
      exact normal_mem k 980
  · rw [show a k b*normalRep k 882=0 from arrow_incompatible k b 42 41 [67, 32, 61, 35, 55, 27, 58, 34] (normal_endpoints 882) h]
    exact Submodule.zero_mem _
lemma extension_883_17 : a k 17*normalRep k 883=normalRep k 981 := by
  change a k 17*walk k 42 [67, 32, 61, 35, 55, 27, 59, 50]=walk k 42 [67, 32, 61, 35, 55, 27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_683 (a k) (relation_zero k) (e k 42)
lemma arrow_span_883 (b : Fin 75) : a k b*normalRep k 883 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_883_17 k]
      exact normal_mem k 981
  · rw [show a k b*normalRep k 883=0 from arrow_incompatible k b 42 16 [67, 32, 61, 35, 55, 27, 59, 50] (normal_endpoints 883) h]
    exact Submodule.zero_mem _
lemma extension_884_57 : a k 57*normalRep k 884=normalRep k 983 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 18, 9, 41, 44] 57).symm
lemma extension_884_58 : a k 58*normalRep k 884=normalRep k 984 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 18, 9, 41, 44] 58).symm
lemma extension_884_59 : a k 59*normalRep k 884=0 := by
  change a k 59*walk k 43 [69, 8, 66, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_645 (a k) (relation_zero k) (e k 43)
lemma arrow_span_884 (b : Fin 75) : a k b*normalRep k 884 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_884_57 k]
      exact normal_mem k 983
    · rw [extension_884_58 k]
      exact normal_mem k 984
    · rw [extension_884_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 884=0 from arrow_incompatible k b 43 39 [69, 8, 66, 24, 18, 9, 41, 44] (normal_endpoints 884) h]
    exact Submodule.zero_mem _
lemma extension_885_1 : a k 1*normalRep k 885=normalRep k 984 := by
  change a k 1*walk k 43 [69, 8, 66, 24, 19, 53, 54, 15]=walk k 43 [69, 8, 66, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_643 (a k) (relation_zero k) (e k 43)
lemma arrow_span_885 (b : Fin 75) : a k b*normalRep k 885 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_885_1 k]
      exact normal_mem k 984
  · rw [show a k b*normalRep k 885=0 from arrow_incompatible k b 43 1 [69, 8, 66, 24, 19, 53, 54, 15] (normal_endpoints 885) h]
    exact Submodule.zero_mem _
lemma extension_886_1 : a k 1*normalRep k 886=normalRep k 985 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 60, 4, 54, 15] 1).symm
lemma arrow_span_886 (b : Fin 75) : a k b*normalRep k 886 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_886_1 k]
      exact normal_mem k 985
  · rw [show a k b*normalRep k 886=0 from arrow_incompatible k b 43 1 [70, 22, 3, 40, 60, 4, 54, 15] (normal_endpoints 886) h]
    exact Submodule.zero_mem _
lemma extension_887_57 : a k 57*normalRep k 887=normalRep k 986 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 60, 4, 54, 16] 57).symm
lemma extension_887_58 : a k 58*normalRep k 887=normalRep k 985 := by
  change a k 58*walk k 43 [70, 22, 3, 40, 60, 4, 54, 16]=walk k 43 [70, 22, 3, 40, 60, 4, 54, 15, 1]
  rw [← walk_snoc]
  exact Universal.mul_reduced_644 (a k) (relation_zero k) (e k 43)
lemma extension_887_59 : a k 59*normalRep k 887=0 := by
  change a k 59*walk k 43 [70, 22, 3, 40, 60, 4, 54, 16]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_646 (a k) (relation_zero k) (e k 43)
lemma arrow_span_887 (b : Fin 75) : a k b*normalRep k 887 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_887_57 k]
      exact normal_mem k 986
    · rw [extension_887_58 k]
      exact normal_mem k 985
    · rw [extension_887_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 887=0 from arrow_incompatible k b 43 39 [70, 22, 3, 40, 60, 4, 54, 16] (normal_endpoints 887) h]
    exact Submodule.zero_mem _
lemma extension_888_5 : a k 5*normalRep k 888=normalRep k 987 := by
  exact (walk_snoc k 44 [72, 37, 24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_888 (b : Fin 75) : a k b*normalRep k 888 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_888_5 k]
      exact normal_mem k 987
  · rw [show a k b*normalRep k 888=0 from arrow_incompatible k b 44 5 [72, 37, 24, 18, 9, 41, 44, 57] (normal_endpoints 888) h]
    exact Submodule.zero_mem _
lemma extension_889_33 : a k 33*normalRep k 889=0 := by
  change a k 33*walk k 44 [72, 37, 24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_622 (a k) (relation_zero k) (e k 44)
lemma extension_889_34 : a k 34*normalRep k 889=normalRep k 987 := by
  change a k 34*walk k 44 [72, 37, 24, 18, 9, 41, 44, 58]=walk k 44 [72, 37, 24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_694 (a k) (relation_zero k) (e k 44)
lemma arrow_span_889 (b : Fin 75) : a k b*normalRep k 889 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_889_33 k]
      exact Submodule.zero_mem _
    · rw [extension_889_34 k]
      exact normal_mem k 987
  · rw [show a k b*normalRep k 889=0 from arrow_incompatible k b 44 26 [72, 37, 24, 18, 9, 41, 44, 58] (normal_endpoints 889) h]
    exact Submodule.zero_mem _
lemma extension_890_33 : a k 33*normalRep k 890=normalRep k 988 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58] 33).symm
lemma extension_890_34 : a k 34*normalRep k 890=normalRep k 989 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 58] 34).symm
lemma arrow_span_890 (b : Fin 75) : a k b*normalRep k 890 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_890_33 k]
      exact normal_mem k 988
    · rw [extension_890_34 k]
      exact normal_mem k 989
  · rw [show a k b*normalRep k 890=0 from arrow_incompatible k b 44 26 [73, 67, 32, 61, 35, 55, 27, 58] (normal_endpoints 890) h]
    exact Submodule.zero_mem _
lemma extension_891_50 : a k 50*normalRep k 891=normalRep k 990 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35, 55, 27, 59] 50).symm
lemma extension_891_51 : a k 51*normalRep k 891=normalRep k 989 := by
  change a k 51*walk k 44 [73, 67, 32, 61, 35, 55, 27, 59]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_695 (a k) (relation_zero k) (e k 44)
lemma arrow_span_891 (b : Fin 75) : a k b*normalRep k 891 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_891_50 k]
      exact normal_mem k 990
    · rw [extension_891_51 k]
      exact normal_mem k 989
  · rw [show a k b*normalRep k 891=0 from arrow_incompatible k b 44 36 [73, 67, 32, 61, 35, 55, 27, 59] (normal_endpoints 891) h]
    exact Submodule.zero_mem _
lemma extension_892_7 : a k 7*normalRep k 892=normalRep k 990 := by
  change a k 7*walk k 44 [73, 67, 32, 61, 35, 56, 43, 47]=walk k 44 [73, 67, 32, 61, 35, 55, 27, 59, 50]
  rw [← walk_snoc]
  exact Universal.mul_reduced_680 (a k) (relation_zero k) (e k 44)
lemma arrow_span_892 (b : Fin 75) : a k b*normalRep k 892 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_892_7 k]
      exact normal_mem k 990
  · rw [show a k b*normalRep k 892=0 from arrow_incompatible k b 44 7 [73, 67, 32, 61, 35, 56, 43, 47] (normal_endpoints 892) h]
    exact Submodule.zero_mem _
lemma extension_893_60 : a k 60*normalRep k 893=0 := by
  change a k 60*walk k 45 [74, 10, 11, 26, 31, 73, 67, 32]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_668 (a k) (relation_zero k) (e k 45)
lemma extension_893_61 : a k 61*normalRep k 893=normalRep k 991 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32] 61).symm
lemma extension_893_62 : a k 62*normalRep k 893=normalRep k 992 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31, 73, 67, 32] 62).symm
lemma arrow_span_893 (b : Fin 75) : a k b*normalRep k 893 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_893_60 k]
      exact Submodule.zero_mem _
    · rw [extension_893_61 k]
      exact normal_mem k 991
    · rw [extension_893_62 k]
      exact normal_mem k 992
  · rw [show a k b*normalRep k 893=0 from arrow_incompatible k b 45 40 [74, 10, 11, 26, 31, 73, 67, 32] (normal_endpoints 893) h]
    exact Submodule.zero_mem _
lemma extension_894_12 : a k 12*normalRep k 894=normalRep k 991 := by
  change a k 12*walk k 45 [74, 10, 11, 26, 31, 73, 68, 39]=walk k 45 [74, 10, 11, 26, 31, 73, 67, 32, 61]
  rw [← walk_snoc]
  exact Universal.mul_reduced_676 (a k) (relation_zero k) (e k 45)
lemma arrow_span_894 (b : Fin 75) : a k b*normalRep k 894 ∈ normalSpan k := by
  by_cases h : arrowSource b=12
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [12] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_894_12 k]
      exact normal_mem k 991
  · rw [show a k b*normalRep k 894=0 from arrow_incompatible k b 45 12 [74, 10, 11, 26, 31, 73, 68, 39] (normal_endpoints 894) h]
    exact Submodule.zero_mem _
lemma extension_895_20 : a k 20*normalRep k 895=normalRep k 993 := by
  exact (walk_snoc k 3 [3, 40, 60, 4, 54, 15, 1, 34, 63] 20).symm
lemma extension_895_21 : a k 21*normalRep k 895=0 := by
  change a k 21*walk k 3 [3, 40, 60, 4, 54, 15, 1, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_790 (a k) (relation_zero k) (e k 3)
lemma arrow_span_895 (b : Fin 75) : a k b*normalRep k 895 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_895_20 k]
      exact normal_mem k 993
    · rw [extension_895_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 895=0 from arrow_incompatible k b 3 18 [3, 40, 60, 4, 54, 15, 1, 34, 63] (normal_endpoints 895) h]
    exact Submodule.zero_mem _
lemma extension_896_0 : a k 0*normalRep k 896=normalRep k 994 := by
  exact (walk_snoc k 4 [4, 54, 15, 1, 34, 63, 20, 30, 2] 0).symm
lemma arrow_span_896 (b : Fin 75) : a k b*normalRep k 896 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_896_0 k]
      exact normal_mem k 994
  · rw [show a k b*normalRep k 896=0 from arrow_incompatible k b 4 0 [4, 54, 15, 1, 34, 63, 20, 30, 2] (normal_endpoints 896) h]
    exact Submodule.zero_mem _
lemma extension_897_9 : a k 9*normalRep k 897=normalRep k 995 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_897 (b : Fin 75) : a k b*normalRep k 897 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_897_9 k]
      exact normal_mem k 995
  · rw [show a k b*normalRep k 897=0 from arrow_incompatible k b 6 9 [6, 7, 17, 21, 69, 8, 66, 24, 18] (normal_endpoints 897) h]
    exact Submodule.zero_mem _
lemma extension_898_52 : a k 52*normalRep k 898=normalRep k 995 := by
  change a k 52*walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 19]=walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_742 (a k) (relation_zero k) (e k 6)
lemma extension_898_53 : a k 53*normalRep k 898=normalRep k 996 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_898 (b : Fin 75) : a k b*normalRep k 898 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_898_52 k]
      exact normal_mem k 995
    · rw [extension_898_53 k]
      exact normal_mem k 996
  · rw [show a k b*normalRep k 898=0 from arrow_incompatible k b 6 37 [6, 7, 17, 21, 69, 8, 66, 24, 19] (normal_endpoints 898) h]
    exact Submodule.zero_mem _
lemma extension_899_4 : a k 4*normalRep k 899=normalRep k 996 := by
  change a k 4*walk k 6 [6, 7, 17, 21, 69, 8, 66, 25, 60]=walk k 6 [6, 7, 17, 21, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_786 (a k) (relation_zero k) (e k 6)
lemma arrow_span_899 (b : Fin 75) : a k b*normalRep k 899 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_899_4 k]
      exact normal_mem k 996
  · rw [show a k b*normalRep k 899=0 from arrow_incompatible k b 6 4 [6, 7, 17, 21, 69, 8, 66, 25, 60] (normal_endpoints 899) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
