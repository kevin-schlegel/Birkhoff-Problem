import N6NormalData
import N6Reduced0
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_0_0 : a k 0*normalRep k 0=normalRep k 47 := by
  exact (walk_snoc k 0 [] 0).symm
lemma arrow_span_0 (b : Fin 75) : a k b*normalRep k 0 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_0_0 k]
      exact normal_mem k 47
  · rw [show a k b*normalRep k 0=0 from arrow_incompatible k b 0 0 [] (normal_endpoints 0) h]
    exact Submodule.zero_mem _
lemma extension_1_1 : a k 1*normalRep k 1=normalRep k 48 := by
  exact (walk_snoc k 1 [] 1).symm
lemma arrow_span_1 (b : Fin 75) : a k b*normalRep k 1 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_1_1 k]
      exact normal_mem k 48
  · rw [show a k b*normalRep k 1=0 from arrow_incompatible k b 1 1 [] (normal_endpoints 1) h]
    exact Submodule.zero_mem _
lemma extension_2_2 : a k 2*normalRep k 2=normalRep k 49 := by
  exact (walk_snoc k 2 [] 2).symm
lemma arrow_span_2 (b : Fin 75) : a k b*normalRep k 2 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_2_2 k]
      exact normal_mem k 49
  · rw [show a k b*normalRep k 2=0 from arrow_incompatible k b 2 2 [] (normal_endpoints 2) h]
    exact Submodule.zero_mem _
lemma extension_3_3 : a k 3*normalRep k 3=normalRep k 50 := by
  exact (walk_snoc k 3 [] 3).symm
lemma arrow_span_3 (b : Fin 75) : a k b*normalRep k 3 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_3_3 k]
      exact normal_mem k 50
  · rw [show a k b*normalRep k 3=0 from arrow_incompatible k b 3 3 [] (normal_endpoints 3) h]
    exact Submodule.zero_mem _
lemma extension_4_4 : a k 4*normalRep k 4=normalRep k 51 := by
  exact (walk_snoc k 4 [] 4).symm
lemma arrow_span_4 (b : Fin 75) : a k b*normalRep k 4 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_4_4 k]
      exact normal_mem k 51
  · rw [show a k b*normalRep k 4=0 from arrow_incompatible k b 4 4 [] (normal_endpoints 4) h]
    exact Submodule.zero_mem _
lemma extension_5_5 : a k 5*normalRep k 5=normalRep k 52 := by
  exact (walk_snoc k 5 [] 5).symm
lemma arrow_span_5 (b : Fin 75) : a k b*normalRep k 5 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_5_5 k]
      exact normal_mem k 52
  · rw [show a k b*normalRep k 5=0 from arrow_incompatible k b 5 5 [] (normal_endpoints 5) h]
    exact Submodule.zero_mem _
lemma extension_6_6 : a k 6*normalRep k 6=normalRep k 53 := by
  exact (walk_snoc k 6 [] 6).symm
lemma arrow_span_6 (b : Fin 75) : a k b*normalRep k 6 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_6_6 k]
      exact normal_mem k 53
  · rw [show a k b*normalRep k 6=0 from arrow_incompatible k b 6 6 [] (normal_endpoints 6) h]
    exact Submodule.zero_mem _
lemma extension_7_7 : a k 7*normalRep k 7=normalRep k 54 := by
  exact (walk_snoc k 7 [] 7).symm
lemma arrow_span_7 (b : Fin 75) : a k b*normalRep k 7 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_7_7 k]
      exact normal_mem k 54
  · rw [show a k b*normalRep k 7=0 from arrow_incompatible k b 7 7 [] (normal_endpoints 7) h]
    exact Submodule.zero_mem _
lemma extension_8_8 : a k 8*normalRep k 8=normalRep k 55 := by
  exact (walk_snoc k 8 [] 8).symm
lemma arrow_span_8 (b : Fin 75) : a k b*normalRep k 8 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_8_8 k]
      exact normal_mem k 55
  · rw [show a k b*normalRep k 8=0 from arrow_incompatible k b 8 8 [] (normal_endpoints 8) h]
    exact Submodule.zero_mem _
lemma extension_9_9 : a k 9*normalRep k 9=normalRep k 56 := by
  exact (walk_snoc k 9 [] 9).symm
lemma arrow_span_9 (b : Fin 75) : a k b*normalRep k 9 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_9_9 k]
      exact normal_mem k 56
  · rw [show a k b*normalRep k 9=0 from arrow_incompatible k b 9 9 [] (normal_endpoints 9) h]
    exact Submodule.zero_mem _
lemma extension_10_10 : a k 10*normalRep k 10=normalRep k 57 := by
  exact (walk_snoc k 10 [] 10).symm
lemma arrow_span_10 (b : Fin 75) : a k b*normalRep k 10 ∈ normalSpan k := by
  by_cases h : arrowSource b=10
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [10] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_10_10 k]
      exact normal_mem k 57
  · rw [show a k b*normalRep k 10=0 from arrow_incompatible k b 10 10 [] (normal_endpoints 10) h]
    exact Submodule.zero_mem _
lemma extension_11_11 : a k 11*normalRep k 11=normalRep k 58 := by
  exact (walk_snoc k 11 [] 11).symm
lemma arrow_span_11 (b : Fin 75) : a k b*normalRep k 11 ∈ normalSpan k := by
  by_cases h : arrowSource b=11
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [11] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_11_11 k]
      exact normal_mem k 58
  · rw [show a k b*normalRep k 11=0 from arrow_incompatible k b 11 11 [] (normal_endpoints 11) h]
    exact Submodule.zero_mem _
lemma extension_12_12 : a k 12*normalRep k 12=normalRep k 59 := by
  exact (walk_snoc k 12 [] 12).symm
lemma arrow_span_12 (b : Fin 75) : a k b*normalRep k 12 ∈ normalSpan k := by
  by_cases h : arrowSource b=12
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [12] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_12_12 k]
      exact normal_mem k 59
  · rw [show a k b*normalRep k 12=0 from arrow_incompatible k b 12 12 [] (normal_endpoints 12) h]
    exact Submodule.zero_mem _
lemma extension_13_13 : a k 13*normalRep k 13=normalRep k 60 := by
  exact (walk_snoc k 13 [] 13).symm
lemma arrow_span_13 (b : Fin 75) : a k b*normalRep k 13 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_13_13 k]
      exact normal_mem k 60
  · rw [show a k b*normalRep k 13=0 from arrow_incompatible k b 13 13 [] (normal_endpoints 13) h]
    exact Submodule.zero_mem _
lemma extension_14_14 : a k 14*normalRep k 14=normalRep k 61 := by
  exact (walk_snoc k 14 [] 14).symm
lemma arrow_span_14 (b : Fin 75) : a k b*normalRep k 14 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_14_14 k]
      exact normal_mem k 61
  · rw [show a k b*normalRep k 14=0 from arrow_incompatible k b 14 14 [] (normal_endpoints 14) h]
    exact Submodule.zero_mem _
lemma extension_15_15 : a k 15*normalRep k 15=normalRep k 62 := by
  exact (walk_snoc k 15 [] 15).symm
lemma extension_15_16 : a k 16*normalRep k 15=normalRep k 63 := by
  exact (walk_snoc k 15 [] 16).symm
lemma arrow_span_15 (b : Fin 75) : a k b*normalRep k 15 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_15_15 k]
      exact normal_mem k 62
    · rw [extension_15_16 k]
      exact normal_mem k 63
  · rw [show a k b*normalRep k 15=0 from arrow_incompatible k b 15 15 [] (normal_endpoints 15) h]
    exact Submodule.zero_mem _
lemma extension_16_17 : a k 17*normalRep k 16=normalRep k 64 := by
  exact (walk_snoc k 16 [] 17).symm
lemma arrow_span_16 (b : Fin 75) : a k b*normalRep k 16 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_16_17 k]
      exact normal_mem k 64
  · rw [show a k b*normalRep k 16=0 from arrow_incompatible k b 16 16 [] (normal_endpoints 16) h]
    exact Submodule.zero_mem _
lemma extension_17_18 : a k 18*normalRep k 17=normalRep k 65 := by
  exact (walk_snoc k 17 [] 18).symm
lemma extension_17_19 : a k 19*normalRep k 17=normalRep k 66 := by
  exact (walk_snoc k 17 [] 19).symm
lemma arrow_span_17 (b : Fin 75) : a k b*normalRep k 17 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_17_18 k]
      exact normal_mem k 65
    · rw [extension_17_19 k]
      exact normal_mem k 66
  · rw [show a k b*normalRep k 17=0 from arrow_incompatible k b 17 17 [] (normal_endpoints 17) h]
    exact Submodule.zero_mem _
lemma extension_18_20 : a k 20*normalRep k 18=normalRep k 67 := by
  exact (walk_snoc k 18 [] 20).symm
lemma extension_18_21 : a k 21*normalRep k 18=normalRep k 68 := by
  exact (walk_snoc k 18 [] 21).symm
lemma arrow_span_18 (b : Fin 75) : a k b*normalRep k 18 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_18_20 k]
      exact normal_mem k 67
    · rw [extension_18_21 k]
      exact normal_mem k 68
  · rw [show a k b*normalRep k 18=0 from arrow_incompatible k b 18 18 [] (normal_endpoints 18) h]
    exact Submodule.zero_mem _
lemma extension_19_22 : a k 22*normalRep k 19=normalRep k 69 := by
  exact (walk_snoc k 19 [] 22).symm
lemma extension_19_23 : a k 23*normalRep k 19=normalRep k 70 := by
  exact (walk_snoc k 19 [] 23).symm
lemma arrow_span_19 (b : Fin 75) : a k b*normalRep k 19 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_19_22 k]
      exact normal_mem k 69
    · rw [extension_19_23 k]
      exact normal_mem k 70
  · rw [show a k b*normalRep k 19=0 from arrow_incompatible k b 19 19 [] (normal_endpoints 19) h]
    exact Submodule.zero_mem _
lemma extension_20_24 : a k 24*normalRep k 20=normalRep k 71 := by
  exact (walk_snoc k 20 [] 24).symm
lemma extension_20_25 : a k 25*normalRep k 20=normalRep k 72 := by
  exact (walk_snoc k 20 [] 25).symm
lemma arrow_span_20 (b : Fin 75) : a k b*normalRep k 20 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_20_24 k]
      exact normal_mem k 71
    · rw [extension_20_25 k]
      exact normal_mem k 72
  · rw [show a k b*normalRep k 20=0 from arrow_incompatible k b 20 20 [] (normal_endpoints 20) h]
    exact Submodule.zero_mem _
lemma extension_21_26 : a k 26*normalRep k 21=normalRep k 73 := by
  exact (walk_snoc k 21 [] 26).symm
lemma arrow_span_21 (b : Fin 75) : a k b*normalRep k 21 ∈ normalSpan k := by
  by_cases h : arrowSource b=21
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [26] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_21_26 k]
      exact normal_mem k 73
  · rw [show a k b*normalRep k 21=0 from arrow_incompatible k b 21 21 [] (normal_endpoints 21) h]
    exact Submodule.zero_mem _
lemma extension_22_27 : a k 27*normalRep k 22=normalRep k 74 := by
  exact (walk_snoc k 22 [] 27).symm
lemma arrow_span_22 (b : Fin 75) : a k b*normalRep k 22 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_22_27 k]
      exact normal_mem k 74
  · rw [show a k b*normalRep k 22=0 from arrow_incompatible k b 22 22 [] (normal_endpoints 22) h]
    exact Submodule.zero_mem _
lemma extension_23_28 : a k 28*normalRep k 23=normalRep k 75 := by
  exact (walk_snoc k 23 [] 28).symm
lemma extension_23_29 : a k 29*normalRep k 23=normalRep k 76 := by
  exact (walk_snoc k 23 [] 29).symm
lemma arrow_span_23 (b : Fin 75) : a k b*normalRep k 23 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_23_28 k]
      exact normal_mem k 75
    · rw [extension_23_29 k]
      exact normal_mem k 76
  · rw [show a k b*normalRep k 23=0 from arrow_incompatible k b 23 23 [] (normal_endpoints 23) h]
    exact Submodule.zero_mem _
lemma extension_24_30 : a k 30*normalRep k 24=normalRep k 77 := by
  exact (walk_snoc k 24 [] 30).symm
lemma extension_24_31 : a k 31*normalRep k 24=normalRep k 78 := by
  exact (walk_snoc k 24 [] 31).symm
lemma arrow_span_24 (b : Fin 75) : a k b*normalRep k 24 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_24_30 k]
      exact normal_mem k 77
    · rw [extension_24_31 k]
      exact normal_mem k 78
  · rw [show a k b*normalRep k 24=0 from arrow_incompatible k b 24 24 [] (normal_endpoints 24) h]
    exact Submodule.zero_mem _
lemma extension_25_32 : a k 32*normalRep k 25=normalRep k 79 := by
  exact (walk_snoc k 25 [] 32).symm
lemma arrow_span_25 (b : Fin 75) : a k b*normalRep k 25 ∈ normalSpan k := by
  by_cases h : arrowSource b=25
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [32] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_25_32 k]
      exact normal_mem k 79
  · rw [show a k b*normalRep k 25=0 from arrow_incompatible k b 25 25 [] (normal_endpoints 25) h]
    exact Submodule.zero_mem _
lemma extension_26_33 : a k 33*normalRep k 26=normalRep k 80 := by
  exact (walk_snoc k 26 [] 33).symm
lemma extension_26_34 : a k 34*normalRep k 26=normalRep k 81 := by
  exact (walk_snoc k 26 [] 34).symm
lemma arrow_span_26 (b : Fin 75) : a k b*normalRep k 26 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_26_33 k]
      exact normal_mem k 80
    · rw [extension_26_34 k]
      exact normal_mem k 81
  · rw [show a k b*normalRep k 26=0 from arrow_incompatible k b 26 26 [] (normal_endpoints 26) h]
    exact Submodule.zero_mem _
lemma extension_27_35 : a k 35*normalRep k 27=normalRep k 82 := by
  exact (walk_snoc k 27 [] 35).symm
lemma arrow_span_27 (b : Fin 75) : a k b*normalRep k 27 ∈ normalSpan k := by
  by_cases h : arrowSource b=27
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [35] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_27_35 k]
      exact normal_mem k 82
  · rw [show a k b*normalRep k 27=0 from arrow_incompatible k b 27 27 [] (normal_endpoints 27) h]
    exact Submodule.zero_mem _
lemma extension_28_36 : a k 36*normalRep k 28=normalRep k 83 := by
  exact (walk_snoc k 28 [] 36).symm
lemma arrow_span_28 (b : Fin 75) : a k b*normalRep k 28 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_28_36 k]
      exact normal_mem k 83
  · rw [show a k b*normalRep k 28=0 from arrow_incompatible k b 28 28 [] (normal_endpoints 28) h]
    exact Submodule.zero_mem _
lemma extension_29_37 : a k 37*normalRep k 29=normalRep k 84 := by
  exact (walk_snoc k 29 [] 37).symm
lemma extension_29_38 : a k 38*normalRep k 29=normalRep k 85 := by
  exact (walk_snoc k 29 [] 38).symm
lemma arrow_span_29 (b : Fin 75) : a k b*normalRep k 29 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_29_37 k]
      exact normal_mem k 84
    · rw [extension_29_38 k]
      exact normal_mem k 85
  · rw [show a k b*normalRep k 29=0 from arrow_incompatible k b 29 29 [] (normal_endpoints 29) h]
    exact Submodule.zero_mem _
lemma extension_30_39 : a k 39*normalRep k 30=normalRep k 86 := by
  exact (walk_snoc k 30 [] 39).symm
lemma extension_30_40 : a k 40*normalRep k 30=normalRep k 87 := by
  exact (walk_snoc k 30 [] 40).symm
lemma arrow_span_30 (b : Fin 75) : a k b*normalRep k 30 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_30_39 k]
      exact normal_mem k 86
    · rw [extension_30_40 k]
      exact normal_mem k 87
  · rw [show a k b*normalRep k 30=0 from arrow_incompatible k b 30 30 [] (normal_endpoints 30) h]
    exact Submodule.zero_mem _
lemma extension_31_41 : a k 41*normalRep k 31=normalRep k 88 := by
  exact (walk_snoc k 31 [] 41).symm
lemma extension_31_42 : a k 42*normalRep k 31=normalRep k 89 := by
  exact (walk_snoc k 31 [] 42).symm
lemma arrow_span_31 (b : Fin 75) : a k b*normalRep k 31 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_31_41 k]
      exact normal_mem k 88
    · rw [extension_31_42 k]
      exact normal_mem k 89
  · rw [show a k b*normalRep k 31=0 from arrow_incompatible k b 31 31 [] (normal_endpoints 31) h]
    exact Submodule.zero_mem _
lemma extension_32_43 : a k 43*normalRep k 32=normalRep k 90 := by
  exact (walk_snoc k 32 [] 43).symm
lemma extension_32_44 : a k 44*normalRep k 32=normalRep k 91 := by
  exact (walk_snoc k 32 [] 44).symm
lemma arrow_span_32 (b : Fin 75) : a k b*normalRep k 32 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_32_43 k]
      exact normal_mem k 90
    · rw [extension_32_44 k]
      exact normal_mem k 91
  · rw [show a k b*normalRep k 32=0 from arrow_incompatible k b 32 32 [] (normal_endpoints 32) h]
    exact Submodule.zero_mem _
lemma extension_33_45 : a k 45*normalRep k 33=normalRep k 92 := by
  exact (walk_snoc k 33 [] 45).symm
lemma extension_33_46 : a k 46*normalRep k 33=normalRep k 93 := by
  exact (walk_snoc k 33 [] 46).symm
lemma arrow_span_33 (b : Fin 75) : a k b*normalRep k 33 ∈ normalSpan k := by
  by_cases h : arrowSource b=33
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [45, 46] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_33_45 k]
      exact normal_mem k 92
    · rw [extension_33_46 k]
      exact normal_mem k 93
  · rw [show a k b*normalRep k 33=0 from arrow_incompatible k b 33 33 [] (normal_endpoints 33) h]
    exact Submodule.zero_mem _
lemma extension_34_47 : a k 47*normalRep k 34=normalRep k 94 := by
  exact (walk_snoc k 34 [] 47).symm
lemma extension_34_48 : a k 48*normalRep k 34=normalRep k 95 := by
  exact (walk_snoc k 34 [] 48).symm
lemma arrow_span_34 (b : Fin 75) : a k b*normalRep k 34 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_34_47 k]
      exact normal_mem k 94
    · rw [extension_34_48 k]
      exact normal_mem k 95
  · rw [show a k b*normalRep k 34=0 from arrow_incompatible k b 34 34 [] (normal_endpoints 34) h]
    exact Submodule.zero_mem _
lemma extension_35_49 : a k 49*normalRep k 35=normalRep k 96 := by
  exact (walk_snoc k 35 [] 49).symm
lemma arrow_span_35 (b : Fin 75) : a k b*normalRep k 35 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_35_49 k]
      exact normal_mem k 96
  · rw [show a k b*normalRep k 35=0 from arrow_incompatible k b 35 35 [] (normal_endpoints 35) h]
    exact Submodule.zero_mem _
lemma extension_36_50 : a k 50*normalRep k 36=normalRep k 97 := by
  exact (walk_snoc k 36 [] 50).symm
lemma extension_36_51 : a k 51*normalRep k 36=normalRep k 98 := by
  exact (walk_snoc k 36 [] 51).symm
lemma arrow_span_36 (b : Fin 75) : a k b*normalRep k 36 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_36_50 k]
      exact normal_mem k 97
    · rw [extension_36_51 k]
      exact normal_mem k 98
  · rw [show a k b*normalRep k 36=0 from arrow_incompatible k b 36 36 [] (normal_endpoints 36) h]
    exact Submodule.zero_mem _
lemma extension_37_52 : a k 52*normalRep k 37=normalRep k 99 := by
  exact (walk_snoc k 37 [] 52).symm
lemma extension_37_53 : a k 53*normalRep k 37=normalRep k 100 := by
  exact (walk_snoc k 37 [] 53).symm
lemma arrow_span_37 (b : Fin 75) : a k b*normalRep k 37 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_37_52 k]
      exact normal_mem k 99
    · rw [extension_37_53 k]
      exact normal_mem k 100
  · rw [show a k b*normalRep k 37=0 from arrow_incompatible k b 37 37 [] (normal_endpoints 37) h]
    exact Submodule.zero_mem _
lemma extension_38_54 : a k 54*normalRep k 38=normalRep k 101 := by
  exact (walk_snoc k 38 [] 54).symm
lemma extension_38_55 : a k 55*normalRep k 38=normalRep k 102 := by
  exact (walk_snoc k 38 [] 55).symm
lemma extension_38_56 : a k 56*normalRep k 38=normalRep k 103 := by
  exact (walk_snoc k 38 [] 56).symm
lemma arrow_span_38 (b : Fin 75) : a k b*normalRep k 38 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_38_54 k]
      exact normal_mem k 101
    · rw [extension_38_55 k]
      exact normal_mem k 102
    · rw [extension_38_56 k]
      exact normal_mem k 103
  · rw [show a k b*normalRep k 38=0 from arrow_incompatible k b 38 38 [] (normal_endpoints 38) h]
    exact Submodule.zero_mem _
lemma extension_39_57 : a k 57*normalRep k 39=normalRep k 104 := by
  exact (walk_snoc k 39 [] 57).symm
lemma extension_39_58 : a k 58*normalRep k 39=normalRep k 105 := by
  exact (walk_snoc k 39 [] 58).symm
lemma extension_39_59 : a k 59*normalRep k 39=normalRep k 106 := by
  exact (walk_snoc k 39 [] 59).symm
lemma arrow_span_39 (b : Fin 75) : a k b*normalRep k 39 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_39_57 k]
      exact normal_mem k 104
    · rw [extension_39_58 k]
      exact normal_mem k 105
    · rw [extension_39_59 k]
      exact normal_mem k 106
  · rw [show a k b*normalRep k 39=0 from arrow_incompatible k b 39 39 [] (normal_endpoints 39) h]
    exact Submodule.zero_mem _
lemma extension_40_60 : a k 60*normalRep k 40=normalRep k 107 := by
  exact (walk_snoc k 40 [] 60).symm
lemma extension_40_61 : a k 61*normalRep k 40=normalRep k 108 := by
  exact (walk_snoc k 40 [] 61).symm
lemma extension_40_62 : a k 62*normalRep k 40=normalRep k 109 := by
  exact (walk_snoc k 40 [] 62).symm
lemma arrow_span_40 (b : Fin 75) : a k b*normalRep k 40 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_40_60 k]
      exact normal_mem k 107
    · rw [extension_40_61 k]
      exact normal_mem k 108
    · rw [extension_40_62 k]
      exact normal_mem k 109
  · rw [show a k b*normalRep k 40=0 from arrow_incompatible k b 40 40 [] (normal_endpoints 40) h]
    exact Submodule.zero_mem _
lemma extension_41_63 : a k 63*normalRep k 41=normalRep k 110 := by
  exact (walk_snoc k 41 [] 63).symm
lemma extension_41_64 : a k 64*normalRep k 41=normalRep k 111 := by
  exact (walk_snoc k 41 [] 64).symm
lemma extension_41_65 : a k 65*normalRep k 41=normalRep k 112 := by
  exact (walk_snoc k 41 [] 65).symm
lemma arrow_span_41 (b : Fin 75) : a k b*normalRep k 41 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_41_63 k]
      exact normal_mem k 110
    · rw [extension_41_64 k]
      exact normal_mem k 111
    · rw [extension_41_65 k]
      exact normal_mem k 112
  · rw [show a k b*normalRep k 41=0 from arrow_incompatible k b 41 41 [] (normal_endpoints 41) h]
    exact Submodule.zero_mem _
lemma extension_42_66 : a k 66*normalRep k 42=normalRep k 113 := by
  exact (walk_snoc k 42 [] 66).symm
lemma extension_42_67 : a k 67*normalRep k 42=normalRep k 114 := by
  exact (walk_snoc k 42 [] 67).symm
lemma extension_42_68 : a k 68*normalRep k 42=normalRep k 115 := by
  exact (walk_snoc k 42 [] 68).symm
lemma arrow_span_42 (b : Fin 75) : a k b*normalRep k 42 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_42_66 k]
      exact normal_mem k 113
    · rw [extension_42_67 k]
      exact normal_mem k 114
    · rw [extension_42_68 k]
      exact normal_mem k 115
  · rw [show a k b*normalRep k 42=0 from arrow_incompatible k b 42 42 [] (normal_endpoints 42) h]
    exact Submodule.zero_mem _
lemma extension_43_69 : a k 69*normalRep k 43=normalRep k 116 := by
  exact (walk_snoc k 43 [] 69).symm
lemma extension_43_70 : a k 70*normalRep k 43=normalRep k 117 := by
  exact (walk_snoc k 43 [] 70).symm
lemma extension_43_71 : a k 71*normalRep k 43=normalRep k 118 := by
  exact (walk_snoc k 43 [] 71).symm
lemma arrow_span_43 (b : Fin 75) : a k b*normalRep k 43 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_43_69 k]
      exact normal_mem k 116
    · rw [extension_43_70 k]
      exact normal_mem k 117
    · rw [extension_43_71 k]
      exact normal_mem k 118
  · rw [show a k b*normalRep k 43=0 from arrow_incompatible k b 43 43 [] (normal_endpoints 43) h]
    exact Submodule.zero_mem _
lemma extension_44_72 : a k 72*normalRep k 44=normalRep k 119 := by
  exact (walk_snoc k 44 [] 72).symm
lemma extension_44_73 : a k 73*normalRep k 44=normalRep k 120 := by
  exact (walk_snoc k 44 [] 73).symm
lemma arrow_span_44 (b : Fin 75) : a k b*normalRep k 44 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_44_72 k]
      exact normal_mem k 119
    · rw [extension_44_73 k]
      exact normal_mem k 120
  · rw [show a k b*normalRep k 44=0 from arrow_incompatible k b 44 44 [] (normal_endpoints 44) h]
    exact Submodule.zero_mem _
lemma extension_45_74 : a k 74*normalRep k 45=normalRep k 121 := by
  exact (walk_snoc k 45 [] 74).symm
lemma arrow_span_45 (b : Fin 75) : a k b*normalRep k 45 ∈ normalSpan k := by
  by_cases h : arrowSource b=45
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [74] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_45_74 k]
      exact normal_mem k 121
  · rw [show a k b*normalRep k 45=0 from arrow_incompatible k b 45 45 [] (normal_endpoints 45) h]
    exact Submodule.zero_mem _
lemma arrow_span_46 (b : Fin 75) : a k b*normalRep k 46 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 46=0 from arrow_incompatible k b 46 46 [] (normal_endpoints 46) h]
    exact Submodule.zero_mem _
lemma arrow_span_47 (b : Fin 75) : a k b*normalRep k 47 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 47=0 from arrow_incompatible k b 0 46 [0] (normal_endpoints 47) h]
    exact Submodule.zero_mem _
lemma extension_48_33 : a k 33*normalRep k 48=0 := by
  change a k 33*walk k 1 [1]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_0 (a k) (relation_zero k) (e k 1)
lemma extension_48_34 : a k 34*normalRep k 48=normalRep k 122 := by
  exact (walk_snoc k 1 [1] 34).symm
lemma arrow_span_48 (b : Fin 75) : a k b*normalRep k 48 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_48_33 k]
      exact Submodule.zero_mem _
    · rw [extension_48_34 k]
      exact normal_mem k 122
  · rw [show a k b*normalRep k 48=0 from arrow_incompatible k b 1 26 [1] (normal_endpoints 48) h]
    exact Submodule.zero_mem _
lemma extension_49_0 : a k 0*normalRep k 49=normalRep k 123 := by
  exact (walk_snoc k 2 [2] 0).symm
lemma arrow_span_49 (b : Fin 75) : a k b*normalRep k 49 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_49_0 k]
      exact normal_mem k 123
  · rw [show a k b*normalRep k 49=0 from arrow_incompatible k b 2 0 [2] (normal_endpoints 49) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
