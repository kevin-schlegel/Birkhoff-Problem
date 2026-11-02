import N6NormalData
import N6Reduced5
import N6Reduced6
import N6Reduced7
import N6Reduced8
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_550_43 : a k 43*normalRep k 550=0 := by
  change a k 43*walk k 42 [66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_325 (a k) (relation_zero k) (e k 42)
lemma extension_550_44 : a k 44*normalRep k 550=normalRep k 666 := by
  exact (walk_snoc k 42 [66, 24, 18, 9, 41] 44).symm
lemma arrow_span_550 (b : Fin 75) : a k b*normalRep k 550 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_550_43 k]
      exact Submodule.zero_mem _
    · rw [extension_550_44 k]
      exact normal_mem k 666
  · rw [show a k b*normalRep k 550=0 from arrow_incompatible k b 42 32 [66, 24, 18, 9, 41] (normal_endpoints 550) h]
    exact Submodule.zero_mem _
lemma extension_551_15 : a k 15*normalRep k 551=normalRep k 667 := by
  exact (walk_snoc k 42 [66, 24, 19, 53, 54] 15).symm
lemma extension_551_16 : a k 16*normalRep k 551=normalRep k 666 := by
  change a k 16*walk k 42 [66, 24, 19, 53, 54]=walk k 42 [66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_394 (a k) (relation_zero k) (e k 42)
lemma arrow_span_551 (b : Fin 75) : a k b*normalRep k 551 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_551_15 k]
      exact normal_mem k 667
    · rw [extension_551_16 k]
      exact normal_mem k 666
  · rw [show a k b*normalRep k 551=0 from arrow_incompatible k b 42 15 [66, 24, 19, 53, 54] (normal_endpoints 551) h]
    exact Submodule.zero_mem _
lemma extension_552_27 : a k 27*normalRep k 552=normalRep k 668 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 55] 27).symm
lemma arrow_span_552 (b : Fin 75) : a k b*normalRep k 552 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_552_27 k]
      exact normal_mem k 668
  · rw [show a k b*normalRep k 552=0 from arrow_incompatible k b 42 22 [67, 32, 61, 35, 55] (normal_endpoints 552) h]
    exact Submodule.zero_mem _
lemma extension_553_43 : a k 43*normalRep k 553=normalRep k 669 := by
  exact (walk_snoc k 42 [67, 32, 61, 35, 56] 43).symm
lemma extension_553_44 : a k 44*normalRep k 553=normalRep k 668 := by
  change a k 44*walk k 42 [67, 32, 61, 35, 56]=walk k 42 [67, 32, 61, 35, 55, 27]
  rw [← walk_snoc]
  exact Universal.mul_reduced_395 (a k) (relation_zero k) (e k 42)
lemma arrow_span_553 (b : Fin 75) : a k b*normalRep k 553 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_553_43 k]
      exact normal_mem k 669
    · rw [extension_553_44 k]
      exact normal_mem k 668
  · rw [show a k b*normalRep k 553=0 from arrow_incompatible k b 42 32 [67, 32, 61, 35, 56] (normal_endpoints 553) h]
    exact Submodule.zero_mem _
lemma extension_554_45 : a k 45*normalRep k 554=normalRep k 670 := by
  exact (walk_snoc k 42 [67, 32, 62, 52, 42] 45).symm
lemma extension_554_46 : a k 46*normalRep k 554=normalRep k 669 := by
  change a k 46*walk k 42 [67, 32, 62, 52, 42]=walk k 42 [67, 32, 61, 35, 56, 43]
  rw [← walk_snoc]
  exact Universal.mul_reduced_376 (a k) (relation_zero k) (e k 42)
lemma arrow_span_554 (b : Fin 75) : a k b*normalRep k 554 ∈ normalSpan k := by
  by_cases h : arrowSource b=33
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [45, 46] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_554_45 k]
      exact normal_mem k 670
    · rw [extension_554_46 k]
      exact normal_mem k 669
  · rw [show a k b*normalRep k 554=0 from arrow_incompatible k b 42 33 [67, 32, 62, 52, 42] (normal_endpoints 554) h]
    exact Submodule.zero_mem _
lemma extension_555_9 : a k 9*normalRep k 555=normalRep k 671 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 18] 9).symm
lemma arrow_span_555 (b : Fin 75) : a k b*normalRep k 555 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_555_9 k]
      exact normal_mem k 671
  · rw [show a k b*normalRep k 555=0 from arrow_incompatible k b 43 9 [69, 8, 66, 24, 18] (normal_endpoints 555) h]
    exact Submodule.zero_mem _
lemma extension_556_52 : a k 52*normalRep k 556=normalRep k 671 := by
  change a k 52*walk k 43 [69, 8, 66, 24, 19]=walk k 43 [69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_345 (a k) (relation_zero k) (e k 43)
lemma extension_556_53 : a k 53*normalRep k 556=normalRep k 672 := by
  exact (walk_snoc k 43 [69, 8, 66, 24, 19] 53).symm
lemma arrow_span_556 (b : Fin 75) : a k b*normalRep k 556 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_556_52 k]
      exact normal_mem k 671
    · rw [extension_556_53 k]
      exact normal_mem k 672
  · rw [show a k b*normalRep k 556=0 from arrow_incompatible k b 43 37 [69, 8, 66, 24, 19] (normal_endpoints 556) h]
    exact Submodule.zero_mem _
lemma extension_557_4 : a k 4*normalRep k 557=normalRep k 672 := by
  change a k 4*walk k 43 [69, 8, 66, 25, 60]=walk k 43 [69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_402 (a k) (relation_zero k) (e k 43)
lemma arrow_span_557 (b : Fin 75) : a k b*normalRep k 557 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_557_4 k]
      exact normal_mem k 672
  · rw [show a k b*normalRep k 557=0 from arrow_incompatible k b 43 4 [69, 8, 66, 25, 60] (normal_endpoints 557) h]
    exact Submodule.zero_mem _
lemma extension_558_4 : a k 4*normalRep k 558=normalRep k 673 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 60] 4).symm
lemma arrow_span_558 (b : Fin 75) : a k b*normalRep k 558 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_558_4 k]
      exact normal_mem k 673
  · rw [show a k b*normalRep k 558=0 from arrow_incompatible k b 43 4 [70, 22, 3, 40, 60] (normal_endpoints 558) h]
    exact Submodule.zero_mem _
lemma extension_559_52 : a k 52*normalRep k 559=normalRep k 674 := by
  exact (walk_snoc k 43 [70, 22, 3, 40, 62] 52).symm
lemma extension_559_53 : a k 53*normalRep k 559=normalRep k 673 := by
  change a k 53*walk k 43 [70, 22, 3, 40, 62]=walk k 43 [70, 22, 3, 40, 60, 4]
  rw [← walk_snoc]
  exact Universal.mul_reduced_403 (a k) (relation_zero k) (e k 43)
lemma arrow_span_559 (b : Fin 75) : a k b*normalRep k 559 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_559_52 k]
      exact normal_mem k 674
    · rw [extension_559_53 k]
      exact normal_mem k 673
  · rw [show a k b*normalRep k 559=0 from arrow_incompatible k b 43 37 [70, 22, 3, 40, 62] (normal_endpoints 559) h]
    exact Submodule.zero_mem _
lemma extension_560_9 : a k 9*normalRep k 560=normalRep k 674 := by
  change a k 9*walk k 43 [70, 23, 66, 24, 18]=walk k 43 [70, 22, 3, 40, 62, 52]
  rw [← walk_snoc]
  exact Universal.mul_reduced_346 (a k) (relation_zero k) (e k 43)
lemma arrow_span_560 (b : Fin 75) : a k b*normalRep k 560 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_560_9 k]
      exact normal_mem k 674
  · rw [show a k b*normalRep k 560=0 from arrow_incompatible k b 43 9 [70, 23, 66, 24, 18] (normal_endpoints 560) h]
    exact Submodule.zero_mem _
lemma extension_561_41 : a k 41*normalRep k 561=normalRep k 675 := by
  exact (walk_snoc k 44 [72, 37, 24, 18, 9] 41).symm
lemma extension_561_42 : a k 42*normalRep k 561=0 := by
  change a k 42*walk k 44 [72, 37, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_336 (a k) (relation_zero k) (e k 44)
lemma arrow_span_561 (b : Fin 75) : a k b*normalRep k 561 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_561_41 k]
      exact normal_mem k 675
    · rw [extension_561_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 561=0 from arrow_incompatible k b 44 31 [72, 37, 24, 18, 9] (normal_endpoints 561) h]
    exact Submodule.zero_mem _
lemma extension_562_54 : a k 54*normalRep k 562=normalRep k 676 := by
  exact (walk_snoc k 44 [72, 37, 24, 19, 53] 54).symm
lemma extension_562_55 : a k 55*normalRep k 562=0 := by
  change a k 55*walk k 44 [72, 37, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_322 (a k) (relation_zero k) (e k 44)
lemma extension_562_56 : a k 56*normalRep k 562=normalRep k 675 := by
  change a k 56*walk k 44 [72, 37, 24, 19, 53]=walk k 44 [72, 37, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_390 (a k) (relation_zero k) (e k 44)
lemma arrow_span_562 (b : Fin 75) : a k b*normalRep k 562 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_562_54 k]
      exact normal_mem k 676
    · rw [extension_562_55 k]
      exact Submodule.zero_mem _
    · rw [extension_562_56 k]
      exact normal_mem k 675
  · rw [show a k b*normalRep k 562=0 from arrow_incompatible k b 44 38 [72, 37, 24, 19, 53] (normal_endpoints 562) h]
    exact Submodule.zero_mem _
lemma extension_563_54 : a k 54*normalRep k 563=0 := by
  change a k 54*walk k 44 [73, 67, 32, 61, 35]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_369 (a k) (relation_zero k) (e k 44)
lemma extension_563_55 : a k 55*normalRep k 563=normalRep k 677 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35] 55).symm
lemma extension_563_56 : a k 56*normalRep k 563=normalRep k 678 := by
  exact (walk_snoc k 44 [73, 67, 32, 61, 35] 56).symm
lemma arrow_span_563 (b : Fin 75) : a k b*normalRep k 563 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_563_54 k]
      exact Submodule.zero_mem _
    · rw [extension_563_55 k]
      exact normal_mem k 677
    · rw [extension_563_56 k]
      exact normal_mem k 678
  · rw [show a k b*normalRep k 563=0 from arrow_incompatible k b 44 38 [73, 67, 32, 61, 35] (normal_endpoints 563) h]
    exact Submodule.zero_mem _
lemma extension_564_41 : a k 41*normalRep k 564=normalRep k 678 := by
  change a k 41*walk k 44 [73, 67, 32, 62, 52]=walk k 44 [73, 67, 32, 61, 35, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_391 (a k) (relation_zero k) (e k 44)
lemma extension_564_42 : a k 42*normalRep k 564=normalRep k 679 := by
  exact (walk_snoc k 44 [73, 67, 32, 62, 52] 42).symm
lemma arrow_span_564 (b : Fin 75) : a k b*normalRep k 564 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_564_41 k]
      exact normal_mem k 678
    · rw [extension_564_42 k]
      exact normal_mem k 679
  · rw [show a k b*normalRep k 564=0 from arrow_incompatible k b 44 31 [73, 67, 32, 62, 52] (normal_endpoints 564) h]
    exact Submodule.zero_mem _
lemma extension_565_72 : a k 72*normalRep k 565=0 := by
  change a k 72*walk k 45 [74, 10, 11, 26, 31]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_365 (a k) (relation_zero k) (e k 45)
lemma extension_565_73 : a k 73*normalRep k 565=normalRep k 680 := by
  exact (walk_snoc k 45 [74, 10, 11, 26, 31] 73).symm
lemma arrow_span_565 (b : Fin 75) : a k b*normalRep k 565 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_565_72 k]
      exact Submodule.zero_mem _
    · rw [extension_565_73 k]
      exact normal_mem k 680
  · rw [show a k b*normalRep k 565=0 from arrow_incompatible k b 45 44 [74, 10, 11, 26, 31] (normal_endpoints 565) h]
    exact Submodule.zero_mem _
lemma extension_566_0 : a k 0*normalRep k 566=normalRep k 681 := by
  exact (walk_snoc k 1 [1, 34, 63, 20, 30, 2] 0).symm
lemma arrow_span_566 (b : Fin 75) : a k b*normalRep k 566 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_566_0 k]
      exact normal_mem k 681
  · rw [show a k b*normalRep k 566=0 from arrow_incompatible k b 1 0 [1, 34, 63, 20, 30, 2] (normal_endpoints 566) h]
    exact Submodule.zero_mem _
lemma extension_567_1 : a k 1*normalRep k 567=normalRep k 682 := by
  exact (walk_snoc k 3 [3, 40, 60, 4, 54, 15] 1).symm
lemma arrow_span_567 (b : Fin 75) : a k b*normalRep k 567 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_567_1 k]
      exact normal_mem k 682
  · rw [show a k b*normalRep k 567=0 from arrow_incompatible k b 3 1 [3, 40, 60, 4, 54, 15] (normal_endpoints 567) h]
    exact Submodule.zero_mem _
lemma extension_568_57 : a k 57*normalRep k 568=normalRep k 683 := by
  exact (walk_snoc k 3 [3, 40, 60, 4, 54, 16] 57).symm
lemma extension_568_58 : a k 58*normalRep k 568=normalRep k 682 := by
  change a k 58*walk k 3 [3, 40, 60, 4, 54, 16]=walk k 3 [3, 40, 60, 4, 54, 15, 1]
  rw [← walk_snoc]
  exact Universal.mul_reduced_442 (a k) (relation_zero k) (e k 3)
lemma extension_568_59 : a k 59*normalRep k 568=0 := by
  change a k 59*walk k 3 [3, 40, 60, 4, 54, 16]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_445 (a k) (relation_zero k) (e k 3)
lemma arrow_span_568 (b : Fin 75) : a k b*normalRep k 568 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_568_57 k]
      exact normal_mem k 683
    · rw [extension_568_58 k]
      exact normal_mem k 682
    · rw [extension_568_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 568=0 from arrow_incompatible k b 3 39 [3, 40, 60, 4, 54, 16] (normal_endpoints 568) h]
    exact Submodule.zero_mem _
lemma extension_569_20 : a k 20*normalRep k 569=normalRep k 684 := by
  exact (walk_snoc k 4 [4, 54, 15, 1, 34, 63] 20).symm
lemma extension_569_21 : a k 21*normalRep k 569=0 := by
  change a k 21*walk k 4 [4, 54, 15, 1, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_503 (a k) (relation_zero k) (e k 4)
lemma arrow_span_569 (b : Fin 75) : a k b*normalRep k 569 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_569_20 k]
      exact normal_mem k 684
    · rw [extension_569_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 569=0 from arrow_incompatible k b 4 18 [4, 54, 15, 1, 34, 63] (normal_endpoints 569) h]
    exact Submodule.zero_mem _
lemma arrow_span_570 (b : Fin 75) : a k b*normalRep k 570 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 570=0 from arrow_incompatible k b 5 46 [5, 63, 20, 30, 2, 0] (normal_endpoints 570) h]
    exact Submodule.zero_mem _
lemma extension_571_66 : a k 66*normalRep k 571=normalRep k 685 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8] 66).symm
lemma extension_571_67 : a k 67*normalRep k 571=0 := by
  change a k 67*walk k 6 [6, 7, 17, 21, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_438 (a k) (relation_zero k) (e k 6)
lemma extension_571_68 : a k 68*normalRep k 571=normalRep k 686 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69, 8] 68).symm
lemma arrow_span_571 (b : Fin 75) : a k b*normalRep k 571 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_571_66 k]
      exact normal_mem k 685
    · rw [extension_571_67 k]
      exact Submodule.zero_mem _
    · rw [extension_571_68 k]
      exact normal_mem k 686
  · rw [show a k b*normalRep k 571=0 from arrow_incompatible k b 6 42 [6, 7, 17, 21, 69, 8] (normal_endpoints 571) h]
    exact Submodule.zero_mem _
lemma extension_572_3 : a k 3*normalRep k 572=normalRep k 686 := by
  change a k 3*walk k 6 [6, 7, 17, 21, 70, 22]=walk k 6 [6, 7, 17, 21, 69, 8, 68]
  rw [← walk_snoc]
  exact Universal.mul_reduced_457 (a k) (relation_zero k) (e k 6)
lemma arrow_span_572 (b : Fin 75) : a k b*normalRep k 572 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_572_3 k]
      exact normal_mem k 686
  · rw [show a k b*normalRep k 572=0 from arrow_incompatible k b 6 3 [6, 7, 17, 21, 70, 22] (normal_endpoints 572) h]
    exact Submodule.zero_mem _
lemma extension_573_24 : a k 24*normalRep k 573=normalRep k 687 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66] 24).symm
lemma extension_573_25 : a k 25*normalRep k 573=normalRep k 688 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8, 66] 25).symm
lemma arrow_span_573 (b : Fin 75) : a k b*normalRep k 573 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_573_24 k]
      exact normal_mem k 687
    · rw [extension_573_25 k]
      exact normal_mem k 688
  · rw [show a k b*normalRep k 573=0 from arrow_incompatible k b 7 20 [7, 17, 21, 69, 8, 66] (normal_endpoints 573) h]
    exact Submodule.zero_mem _
lemma extension_574_39 : a k 39*normalRep k 574=0 := by
  change a k 39*walk k 7 [7, 17, 21, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_425 (a k) (relation_zero k) (e k 7)
lemma extension_574_40 : a k 40*normalRep k 574=(-normalRep k 688) := by
  change a k 40*walk k 7 [7, 17, 21, 69, 8, 68]=(-walk k 7 [7, 17, 21, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_508 (a k) (relation_zero k) (e k 7)
lemma arrow_span_574 (b : Fin 75) : a k b*normalRep k 574 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_574_39 k]
      exact Submodule.zero_mem _
    · rw [extension_574_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 688)
  · rw [show a k b*normalRep k 574=0 from arrow_incompatible k b 7 30 [7, 17, 21, 69, 8, 68] (normal_endpoints 574) h]
    exact Submodule.zero_mem _
lemma extension_575_43 : a k 43*normalRep k 575=0 := by
  change a k 43*walk k 8 [8, 66, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_431 (a k) (relation_zero k) (e k 8)
lemma extension_575_44 : a k 44*normalRep k 575=normalRep k 689 := by
  exact (walk_snoc k 8 [8, 66, 24, 18, 9, 41] 44).symm
lemma arrow_span_575 (b : Fin 75) : a k b*normalRep k 575 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_575_43 k]
      exact Submodule.zero_mem _
    · rw [extension_575_44 k]
      exact normal_mem k 689
  · rw [show a k b*normalRep k 575=0 from arrow_incompatible k b 8 32 [8, 66, 24, 18, 9, 41] (normal_endpoints 575) h]
    exact Submodule.zero_mem _
lemma extension_576_15 : a k 15*normalRep k 576=normalRep k 690 := by
  exact (walk_snoc k 8 [8, 66, 24, 19, 53, 54] 15).symm
lemma extension_576_16 : a k 16*normalRep k 576=normalRep k 689 := by
  change a k 16*walk k 8 [8, 66, 24, 19, 53, 54]=walk k 8 [8, 66, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_490 (a k) (relation_zero k) (e k 8)
lemma arrow_span_576 (b : Fin 75) : a k b*normalRep k 576 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_576_15 k]
      exact normal_mem k 690
    · rw [extension_576_16 k]
      exact normal_mem k 689
  · rw [show a k b*normalRep k 576=0 from arrow_incompatible k b 8 15 [8, 66, 24, 19, 53, 54] (normal_endpoints 576) h]
    exact Submodule.zero_mem _
lemma extension_577_20 : a k 20*normalRep k 577=normalRep k 691 := by
  exact (walk_snoc k 9 [9, 41, 44, 57, 5, 63] 20).symm
lemma extension_577_21 : a k 21*normalRep k 577=0 := by
  change a k 21*walk k 9 [9, 41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_504 (a k) (relation_zero k) (e k 9)
lemma arrow_span_577 (b : Fin 75) : a k b*normalRep k 577 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_577_20 k]
      exact normal_mem k 691
    · rw [extension_577_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 577=0 from arrow_incompatible k b 9 18 [9, 41, 44, 57, 5, 63] (normal_endpoints 577) h]
    exact Submodule.zero_mem _
lemma extension_578_32 : a k 32*normalRep k 578=normalRep k 692 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 67] 32).symm
lemma arrow_span_578 (b : Fin 75) : a k b*normalRep k 578 ∈ normalSpan k := by
  by_cases h : arrowSource b=25
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [32] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_578_32 k]
      exact normal_mem k 692
  · rw [show a k b*normalRep k 578=0 from arrow_incompatible k b 10 25 [10, 11, 26, 31, 73, 67] (normal_endpoints 578) h]
    exact Submodule.zero_mem _
lemma extension_579_39 : a k 39*normalRep k 579=normalRep k 693 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73, 68] 39).symm
lemma extension_579_40 : a k 40*normalRep k 579=normalRep k 692 := by
  change a k 40*walk k 10 [10, 11, 26, 31, 73, 68]=walk k 10 [10, 11, 26, 31, 73, 67, 32]
  rw [← walk_snoc]
  exact Universal.mul_reduced_509 (a k) (relation_zero k) (e k 10)
lemma arrow_span_579 (b : Fin 75) : a k b*normalRep k 579 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_579_39 k]
      exact normal_mem k 693
    · rw [extension_579_40 k]
      exact normal_mem k 692
  · rw [show a k b*normalRep k 579=0 from arrow_incompatible k b 10 30 [10, 11, 26, 31, 73, 68] (normal_endpoints 579) h]
    exact Submodule.zero_mem _
lemma extension_580_60 : a k 60*normalRep k 580=0 := by
  change a k 60*walk k 11 [11, 26, 31, 73, 67, 32]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_469 (a k) (relation_zero k) (e k 11)
lemma extension_580_61 : a k 61*normalRep k 580=normalRep k 694 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32] 61).symm
lemma extension_580_62 : a k 62*normalRep k 580=normalRep k 695 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67, 32] 62).symm
lemma arrow_span_580 (b : Fin 75) : a k b*normalRep k 580 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_580_60 k]
      exact Submodule.zero_mem _
    · rw [extension_580_61 k]
      exact normal_mem k 694
    · rw [extension_580_62 k]
      exact normal_mem k 695
  · rw [show a k b*normalRep k 580=0 from arrow_incompatible k b 11 40 [11, 26, 31, 73, 67, 32] (normal_endpoints 580) h]
    exact Submodule.zero_mem _
lemma extension_581_12 : a k 12*normalRep k 581=normalRep k 694 := by
  change a k 12*walk k 11 [11, 26, 31, 73, 68, 39]=walk k 11 [11, 26, 31, 73, 67, 32, 61]
  rw [← walk_snoc]
  exact Universal.mul_reduced_477 (a k) (relation_zero k) (e k 11)
lemma arrow_span_581 (b : Fin 75) : a k b*normalRep k 581 ∈ normalSpan k := by
  by_cases h : arrowSource b=12
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [12] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_581_12 k]
      exact normal_mem k 694
  · rw [show a k b*normalRep k 581=0 from arrow_incompatible k b 11 12 [11, 26, 31, 73, 68, 39] (normal_endpoints 581) h]
    exact Submodule.zero_mem _
lemma extension_582_13 : a k 13*normalRep k 582=normalRep k 696 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 33] 13).symm
lemma arrow_span_582 (b : Fin 75) : a k b*normalRep k 582 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_582_13 k]
      exact normal_mem k 696
  · rw [show a k b*normalRep k 582=0 from arrow_incompatible k b 12 13 [12, 35, 55, 27, 58, 33] (normal_endpoints 582) h]
    exact Submodule.zero_mem _
lemma extension_583_63 : a k 63*normalRep k 583=normalRep k 697 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 34] 63).symm
lemma extension_583_64 : a k 64*normalRep k 583=normalRep k 698 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58, 34] 64).symm
lemma extension_583_65 : a k 65*normalRep k 583=normalRep k 696 := by
  change a k 65*walk k 12 [12, 35, 55, 27, 58, 34]=walk k 12 [12, 35, 55, 27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_470 (a k) (relation_zero k) (e k 12)
lemma arrow_span_583 (b : Fin 75) : a k b*normalRep k 583 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_583_63 k]
      exact normal_mem k 697
    · rw [extension_583_64 k]
      exact normal_mem k 698
    · rw [extension_583_65 k]
      exact normal_mem k 696
  · rw [show a k b*normalRep k 583=0 from arrow_incompatible k b 12 41 [12, 35, 55, 27, 58, 34] (normal_endpoints 583) h]
    exact Submodule.zero_mem _
lemma extension_584_17 : a k 17*normalRep k 584=normalRep k 697 := by
  change a k 17*walk k 12 [12, 35, 55, 27, 59, 50]=walk k 12 [12, 35, 55, 27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_485 (a k) (relation_zero k) (e k 12)
lemma arrow_span_584 (b : Fin 75) : a k b*normalRep k 584 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_584_17 k]
      exact normal_mem k 697
  · rw [show a k b*normalRep k 584=0 from arrow_incompatible k b 12 16 [12, 35, 55, 27, 59, 50] (normal_endpoints 584) h]
    exact Submodule.zero_mem _
lemma extension_585_18 : a k 18*normalRep k 585=normalRep k 699 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24] 18).symm
lemma extension_585_19 : a k 19*normalRep k 585=normalRep k 700 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 24] 19).symm
lemma arrow_span_585 (b : Fin 75) : a k b*normalRep k 585 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_585_18 k]
      exact normal_mem k 699
    · rw [extension_585_19 k]
      exact normal_mem k 700
  · rw [show a k b*normalRep k 585=0 from arrow_incompatible k b 13 17 [13, 49, 69, 8, 66, 24] (normal_endpoints 585) h]
    exact Submodule.zero_mem _
lemma extension_586_60 : a k 60*normalRep k 586=normalRep k 701 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66, 25] 60).symm
lemma extension_586_61 : a k 61*normalRep k 586=0 := by
  change a k 61*walk k 13 [13, 49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_460 (a k) (relation_zero k) (e k 13)
lemma extension_586_62 : a k 62*normalRep k 586=normalRep k 700 := by
  change a k 62*walk k 13 [13, 49, 69, 8, 66, 25]=walk k 13 [13, 49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_463 (a k) (relation_zero k) (e k 13)
lemma arrow_span_586 (b : Fin 75) : a k b*normalRep k 586 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_586_60 k]
      exact normal_mem k 701
    · rw [extension_586_61 k]
      exact Submodule.zero_mem _
    · rw [extension_586_62 k]
      exact normal_mem k 700
  · rw [show a k b*normalRep k 586=0 from arrow_incompatible k b 13 40 [13, 49, 69, 8, 66, 25] (normal_endpoints 586) h]
    exact Submodule.zero_mem _
lemma extension_587_14 : a k 14*normalRep k 587=normalRep k 699 := by
  change a k 14*walk k 13 [13, 49, 71, 72, 38, 28]=walk k 13 [13, 49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_467 (a k) (relation_zero k) (e k 13)
lemma arrow_span_587 (b : Fin 75) : a k b*normalRep k 587 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_587_14 k]
      exact normal_mem k 699
  · rw [show a k b*normalRep k 587=0 from arrow_incompatible k b 13 14 [13, 49, 71, 72, 38, 28] (normal_endpoints 587) h]
    exact Submodule.zero_mem _
lemma extension_588_63 : a k 63*normalRep k 588=normalRep k 702 := by
  exact (walk_snoc k 14 [14, 9, 41, 44, 57, 5] 63).symm
lemma extension_588_64 : a k 64*normalRep k 588=0 := by
  change a k 64*walk k 14 [14, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_434 (a k) (relation_zero k) (e k 14)
lemma extension_588_65 : a k 65*normalRep k 588=0 := by
  change a k 65*walk k 14 [14, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_435 (a k) (relation_zero k) (e k 14)
lemma arrow_span_588 (b : Fin 75) : a k b*normalRep k 588 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_588_63 k]
      exact normal_mem k 702
    · rw [extension_588_64 k]
      exact Submodule.zero_mem _
    · rw [extension_588_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 588=0 from arrow_incompatible k b 14 41 [14, 9, 41, 44, 57, 5] (normal_endpoints 588) h]
    exact Submodule.zero_mem _
lemma extension_589_2 : a k 2*normalRep k 589=normalRep k 703 := by
  exact (walk_snoc k 15 [15, 1, 34, 63, 20, 30] 2).symm
lemma arrow_span_589 (b : Fin 75) : a k b*normalRep k 589 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_589_2 k]
      exact normal_mem k 703
  · rw [show a k b*normalRep k 589=0 from arrow_incompatible k b 15 2 [15, 1, 34, 63, 20, 30] (normal_endpoints 589) h]
    exact Submodule.zero_mem _
lemma extension_590_18 : a k 18*normalRep k 590=normalRep k 704 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24] 18).symm
lemma extension_590_19 : a k 19*normalRep k 590=normalRep k 705 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 24] 19).symm
lemma arrow_span_590 (b : Fin 75) : a k b*normalRep k 590 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_590_18 k]
      exact normal_mem k 704
    · rw [extension_590_19 k]
      exact normal_mem k 705
  · rw [show a k b*normalRep k 590=0 from arrow_incompatible k b 16 17 [17, 21, 69, 8, 66, 24] (normal_endpoints 590) h]
    exact Submodule.zero_mem _
lemma extension_591_60 : a k 60*normalRep k 591=normalRep k 706 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66, 25] 60).symm
lemma extension_591_61 : a k 61*normalRep k 591=0 := by
  change a k 61*walk k 16 [17, 21, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_461 (a k) (relation_zero k) (e k 16)
lemma extension_591_62 : a k 62*normalRep k 591=normalRep k 705 := by
  change a k 62*walk k 16 [17, 21, 69, 8, 66, 25]=walk k 16 [17, 21, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_464 (a k) (relation_zero k) (e k 16)
lemma arrow_span_591 (b : Fin 75) : a k b*normalRep k 591 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_591_60 k]
      exact normal_mem k 706
    · rw [extension_591_61 k]
      exact Submodule.zero_mem _
    · rw [extension_591_62 k]
      exact normal_mem k 705
  · rw [show a k b*normalRep k 591=0 from arrow_incompatible k b 16 40 [17, 21, 69, 8, 66, 25] (normal_endpoints 591) h]
    exact Submodule.zero_mem _
lemma extension_592_63 : a k 63*normalRep k 592=normalRep k 707 := by
  exact (walk_snoc k 17 [18, 9, 41, 44, 57, 5] 63).symm
lemma extension_592_64 : a k 64*normalRep k 592=0 := by
  change a k 64*walk k 17 [18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_423 (a k) (relation_zero k) (e k 17)
lemma extension_592_65 : a k 65*normalRep k 592=0 := by
  change a k 65*walk k 17 [18, 9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_436 (a k) (relation_zero k) (e k 17)
lemma arrow_span_592 (b : Fin 75) : a k b*normalRep k 592 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_592_63 k]
      exact normal_mem k 707
    · rw [extension_592_64 k]
      exact Submodule.zero_mem _
    · rw [extension_592_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 592=0 from arrow_incompatible k b 17 41 [18, 9, 41, 44, 57, 5] (normal_endpoints 592) h]
    exact Submodule.zero_mem _
lemma extension_593_9 : a k 9*normalRep k 593=normalRep k 708 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_593 (b : Fin 75) : a k b*normalRep k 593 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_593_9 k]
      exact normal_mem k 708
  · rw [show a k b*normalRep k 593=0 from arrow_incompatible k b 18 9 [21, 69, 8, 66, 24, 18] (normal_endpoints 593) h]
    exact Submodule.zero_mem _
lemma extension_594_52 : a k 52*normalRep k 594=normalRep k 708 := by
  change a k 52*walk k 18 [21, 69, 8, 66, 24, 19]=walk k 18 [21, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_450 (a k) (relation_zero k) (e k 18)
lemma extension_594_53 : a k 53*normalRep k 594=normalRep k 709 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_594 (b : Fin 75) : a k b*normalRep k 594 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_594_52 k]
      exact normal_mem k 708
    · rw [extension_594_53 k]
      exact normal_mem k 709
  · rw [show a k b*normalRep k 594=0 from arrow_incompatible k b 18 37 [21, 69, 8, 66, 24, 19] (normal_endpoints 594) h]
    exact Submodule.zero_mem _
lemma extension_595_4 : a k 4*normalRep k 595=normalRep k 709 := by
  change a k 4*walk k 18 [21, 69, 8, 66, 25, 60]=walk k 18 [21, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_499 (a k) (relation_zero k) (e k 18)
lemma arrow_span_595 (b : Fin 75) : a k b*normalRep k 595 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_595_4 k]
      exact normal_mem k 709
  · rw [show a k b*normalRep k 595=0 from arrow_incompatible k b 18 4 [21, 69, 8, 66, 25, 60] (normal_endpoints 595) h]
    exact Submodule.zero_mem _
lemma extension_596_15 : a k 15*normalRep k 596=normalRep k 710 := by
  exact (walk_snoc k 19 [22, 3, 40, 60, 4, 54] 15).symm
lemma extension_596_16 : a k 16*normalRep k 596=normalRep k 711 := by
  exact (walk_snoc k 19 [22, 3, 40, 60, 4, 54] 16).symm
lemma arrow_span_596 (b : Fin 75) : a k b*normalRep k 596 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_596_15 k]
      exact normal_mem k 710
    · rw [extension_596_16 k]
      exact normal_mem k 711
  · rw [show a k b*normalRep k 596=0 from arrow_incompatible k b 19 15 [22, 3, 40, 60, 4, 54] (normal_endpoints 596) h]
    exact Submodule.zero_mem _
lemma extension_597_43 : a k 43*normalRep k 597=0 := by
  change a k 43*walk k 19 [22, 3, 40, 60, 4, 56]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_432 (a k) (relation_zero k) (e k 19)
lemma extension_597_44 : a k 44*normalRep k 597=normalRep k 711 := by
  change a k 44*walk k 19 [22, 3, 40, 60, 4, 56]=walk k 19 [22, 3, 40, 60, 4, 54, 16]
  rw [← walk_snoc]
  exact Universal.mul_reduced_491 (a k) (relation_zero k) (e k 19)
lemma arrow_span_597 (b : Fin 75) : a k b*normalRep k 597 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_597_43 k]
      exact Submodule.zero_mem _
    · rw [extension_597_44 k]
      exact normal_mem k 711
  · rw [show a k b*normalRep k 597=0 from arrow_incompatible k b 19 32 [22, 3, 40, 60, 4, 56] (normal_endpoints 597) h]
    exact Submodule.zero_mem _
lemma extension_598_5 : a k 5*normalRep k 598=normalRep k 712 := by
  exact (walk_snoc k 20 [24, 18, 9, 41, 44, 57] 5).symm
lemma arrow_span_598 (b : Fin 75) : a k b*normalRep k 598 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_598_5 k]
      exact normal_mem k 712
  · rw [show a k b*normalRep k 598=0 from arrow_incompatible k b 20 5 [24, 18, 9, 41, 44, 57] (normal_endpoints 598) h]
    exact Submodule.zero_mem _
lemma extension_599_33 : a k 33*normalRep k 599=0 := by
  change a k 33*walk k 20 [24, 18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_420 (a k) (relation_zero k) (e k 20)
lemma extension_599_34 : a k 34*normalRep k 599=normalRep k 712 := by
  change a k 34*walk k 20 [24, 18, 9, 41, 44, 58]=walk k 20 [24, 18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_494 (a k) (relation_zero k) (e k 20)
lemma arrow_span_599 (b : Fin 75) : a k b*normalRep k 599 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_599_33 k]
      exact Submodule.zero_mem _
    · rw [extension_599_34 k]
      exact normal_mem k 712
  · rw [show a k b*normalRep k 599=0 from arrow_incompatible k b 20 26 [24, 18, 9, 41, 44, 58] (normal_endpoints 599) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
