import N6NormalData
import N6Reduced5
import N6Reduced6
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_500_17 : a k 17*normalRep k 500=normalRep k 617 := by
  change a k 17*walk k 27 [35, 55, 27, 59, 50]=walk k 27 [35, 55, 27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_386 (a k) (relation_zero k) (e k 27)
lemma arrow_span_500 (b : Fin 75) : a k b*normalRep k 500 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_500_17 k]
      exact normal_mem k 617
  · rw [show a k b*normalRep k 500=0 from arrow_incompatible k b 27 16 [35, 55, 27, 59, 50] (normal_endpoints 500) h]
    exact Submodule.zero_mem _
lemma extension_501_60 : a k 60*normalRep k 501=normalRep k 619 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40] 60).symm
lemma extension_501_61 : a k 61*normalRep k 501=0 := by
  change a k 61*walk k 28 [36, 70, 22, 3, 40]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_356 (a k) (relation_zero k) (e k 28)
lemma extension_501_62 : a k 62*normalRep k 501=normalRep k 620 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40] 62).symm
lemma arrow_span_501 (b : Fin 75) : a k b*normalRep k 501 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_501_60 k]
      exact normal_mem k 619
    · rw [extension_501_61 k]
      exact Submodule.zero_mem _
    · rw [extension_501_62 k]
      exact normal_mem k 620
  · rw [show a k b*normalRep k 501=0 from arrow_incompatible k b 28 40 [36, 70, 22, 3, 40] (normal_endpoints 501) h]
    exact Submodule.zero_mem _
lemma extension_502_18 : a k 18*normalRep k 502=normalRep k 621 := by
  exact (walk_snoc k 28 [36, 70, 23, 66, 24] 18).symm
lemma extension_502_19 : a k 19*normalRep k 502=normalRep k 620 := by
  change a k 19*walk k 28 [36, 70, 23, 66, 24]=walk k 28 [36, 70, 22, 3, 40, 62]
  rw [← walk_snoc]
  exact Universal.mul_reduced_359 (a k) (relation_zero k) (e k 28)
lemma arrow_span_502 (b : Fin 75) : a k b*normalRep k 502 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_502_18 k]
      exact normal_mem k 621
    · rw [extension_502_19 k]
      exact normal_mem k 620
  · rw [show a k b*normalRep k 502=0 from arrow_incompatible k b 28 17 [36, 70, 23, 66, 24] (normal_endpoints 502) h]
    exact Submodule.zero_mem _
lemma extension_503_14 : a k 14*normalRep k 503=normalRep k 621 := by
  change a k 14*walk k 28 [36, 71, 72, 38, 28]=walk k 28 [36, 70, 23, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_363 (a k) (relation_zero k) (e k 28)
lemma arrow_span_503 (b : Fin 75) : a k b*normalRep k 503 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_503_14 k]
      exact normal_mem k 621
  · rw [show a k b*normalRep k 503=0 from arrow_incompatible k b 28 14 [36, 71, 72, 38, 28] (normal_endpoints 503) h]
    exact Submodule.zero_mem _
lemma extension_504_43 : a k 43*normalRep k 504=0 := by
  change a k 43*walk k 29 [37, 24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_324 (a k) (relation_zero k) (e k 29)
lemma extension_504_44 : a k 44*normalRep k 504=normalRep k 622 := by
  exact (walk_snoc k 29 [37, 24, 18, 9, 41] 44).symm
lemma arrow_span_504 (b : Fin 75) : a k b*normalRep k 504 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_504_43 k]
      exact Submodule.zero_mem _
    · rw [extension_504_44 k]
      exact normal_mem k 622
  · rw [show a k b*normalRep k 504=0 from arrow_incompatible k b 29 32 [37, 24, 18, 9, 41] (normal_endpoints 504) h]
    exact Submodule.zero_mem _
lemma extension_505_15 : a k 15*normalRep k 505=normalRep k 623 := by
  exact (walk_snoc k 29 [37, 24, 19, 53, 54] 15).symm
lemma extension_505_16 : a k 16*normalRep k 505=normalRep k 622 := by
  change a k 16*walk k 29 [37, 24, 19, 53, 54]=walk k 29 [37, 24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_393 (a k) (relation_zero k) (e k 29)
lemma arrow_span_505 (b : Fin 75) : a k b*normalRep k 505 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_505_15 k]
      exact normal_mem k 623
    · rw [extension_505_16 k]
      exact normal_mem k 622
  · rw [show a k b*normalRep k 505=0 from arrow_incompatible k b 29 15 [37, 24, 19, 53, 54] (normal_endpoints 505) h]
    exact Submodule.zero_mem _
lemma extension_506_57 : a k 57*normalRep k 506=0 := by
  change a k 57*walk k 30 [39, 12, 35, 55, 27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_362 (a k) (relation_zero k) (e k 30)
lemma extension_506_58 : a k 58*normalRep k 506=normalRep k 624 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27] 58).symm
lemma extension_506_59 : a k 59*normalRep k 506=normalRep k 625 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27] 59).symm
lemma arrow_span_506 (b : Fin 75) : a k b*normalRep k 506 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_506_57 k]
      exact Submodule.zero_mem _
    · rw [extension_506_58 k]
      exact normal_mem k 624
    · rw [extension_506_59 k]
      exact normal_mem k 625
  · rw [show a k b*normalRep k 506=0 from arrow_incompatible k b 30 39 [39, 12, 35, 55, 27] (normal_endpoints 506) h]
    exact Submodule.zero_mem _
lemma extension_507_47 : a k 47*normalRep k 507=normalRep k 626 := by
  exact (walk_snoc k 30 [39, 12, 35, 56, 43] 47).symm
lemma extension_507_48 : a k 48*normalRep k 507=normalRep k 625 := by
  change a k 48*walk k 30 [39, 12, 35, 56, 43]=walk k 30 [39, 12, 35, 55, 27, 59]
  rw [← walk_snoc]
  exact Universal.mul_reduced_378 (a k) (relation_zero k) (e k 30)
lemma arrow_span_507 (b : Fin 75) : a k b*normalRep k 507 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_507_47 k]
      exact normal_mem k 626
    · rw [extension_507_48 k]
      exact normal_mem k 625
  · rw [show a k b*normalRep k 507=0 from arrow_incompatible k b 30 34 [39, 12, 35, 56, 43] (normal_endpoints 507) h]
    exact Submodule.zero_mem _
lemma extension_508_1 : a k 1*normalRep k 508=normalRep k 627 := by
  exact (walk_snoc k 30 [40, 60, 4, 54, 15] 1).symm
lemma arrow_span_508 (b : Fin 75) : a k b*normalRep k 508 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_508_1 k]
      exact normal_mem k 627
  · rw [show a k b*normalRep k 508=0 from arrow_incompatible k b 30 1 [40, 60, 4, 54, 15] (normal_endpoints 508) h]
    exact Submodule.zero_mem _
lemma extension_509_57 : a k 57*normalRep k 509=normalRep k 628 := by
  exact (walk_snoc k 30 [40, 60, 4, 54, 16] 57).symm
lemma extension_509_58 : a k 58*normalRep k 509=normalRep k 627 := by
  change a k 58*walk k 30 [40, 60, 4, 54, 16]=walk k 30 [40, 60, 4, 54, 15, 1]
  rw [← walk_snoc]
  exact Universal.mul_reduced_339 (a k) (relation_zero k) (e k 30)
lemma extension_509_59 : a k 59*normalRep k 509=0 := by
  change a k 59*walk k 30 [40, 60, 4, 54, 16]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_342 (a k) (relation_zero k) (e k 30)
lemma arrow_span_509 (b : Fin 75) : a k b*normalRep k 509 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_509_57 k]
      exact normal_mem k 628
    · rw [extension_509_58 k]
      exact normal_mem k 627
    · rw [extension_509_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 509=0 from arrow_incompatible k b 30 39 [40, 60, 4, 54, 16] (normal_endpoints 509) h]
    exact Submodule.zero_mem _
lemma extension_510_6 : a k 6*normalRep k 510=normalRep k 626 := by
  change a k 6*walk k 30 [40, 62, 52, 42, 45]=walk k 30 [39, 12, 35, 56, 43, 47]
  rw [← walk_snoc]
  exact Universal.mul_reduced_380 (a k) (relation_zero k) (e k 30)
lemma arrow_span_510 (b : Fin 75) : a k b*normalRep k 510 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_510_6 k]
      exact normal_mem k 626
  · rw [show a k b*normalRep k 510=0 from arrow_incompatible k b 30 6 [40, 62, 52, 42, 45] (normal_endpoints 510) h]
    exact Submodule.zero_mem _
lemma extension_511_20 : a k 20*normalRep k 511=0 := by
  change a k 20*walk k 31 [41, 43, 47, 7, 17]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_343 (a k) (relation_zero k) (e k 31)
lemma extension_511_21 : a k 21*normalRep k 511=normalRep k 629 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17] 21).symm
lemma arrow_span_511 (b : Fin 75) : a k b*normalRep k 511 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_511_20 k]
      exact Submodule.zero_mem _
    · rw [extension_511_21 k]
      exact normal_mem k 629
  · rw [show a k b*normalRep k 511=0 from arrow_incompatible k b 31 18 [41, 43, 47, 7, 17] (normal_endpoints 511) h]
    exact Submodule.zero_mem _
lemma extension_512_36 : a k 36*normalRep k 512=normalRep k 630 := by
  exact (walk_snoc k 31 [41, 43, 48, 51, 64] 36).symm
lemma arrow_span_512 (b : Fin 75) : a k b*normalRep k 512 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_512_36 k]
      exact normal_mem k 630
  · rw [show a k b*normalRep k 512=0 from arrow_incompatible k b 31 28 [41, 43, 48, 51, 64] (normal_endpoints 512) h]
    exact Submodule.zero_mem _
lemma extension_513_49 : a k 49*normalRep k 513=(-normalRep k 629) + normalRep k 630 := by
  change a k 49*walk k 31 [41, 43, 48, 51, 65]=(-walk k 31 [41, 43, 47, 7, 17, 21]) + walk k 31 [41, 43, 48, 51, 64, 36]
  rw [← walk_snoc]
  exact Universal.mul_reduced_404 (a k) (relation_zero k) (e k 31)
lemma arrow_span_513 (b : Fin 75) : a k b*normalRep k 513 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_513_49 k]
      exact (normalSpan k).add_mem ((normalSpan k).smul_mem (-1:k) (normal_mem k 629)) (normal_mem k 630)
  · rw [show a k b*normalRep k 513=0 from arrow_incompatible k b 31 35 [41, 43, 48, 51, 65] (normal_endpoints 513) h]
    exact Submodule.zero_mem _
lemma extension_514_20 : a k 20*normalRep k 514=normalRep k 631 := by
  exact (walk_snoc k 31 [41, 44, 57, 5, 63] 20).symm
lemma extension_514_21 : a k 21*normalRep k 514=0 := by
  change a k 21*walk k 31 [41, 44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_405 (a k) (relation_zero k) (e k 31)
lemma arrow_span_514 (b : Fin 75) : a k b*normalRep k 514 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_514_20 k]
      exact normal_mem k 631
    · rw [extension_514_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 514=0 from arrow_incompatible k b 31 18 [41, 44, 57, 5, 63] (normal_endpoints 514) h]
    exact Submodule.zero_mem _
lemma extension_515_69 : a k 69*normalRep k 515=normalRep k 632 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21] 69).symm
lemma extension_515_70 : a k 70*normalRep k 515=normalRep k 633 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21] 70).symm
lemma extension_515_71 : a k 71*normalRep k 515=0 := by
  change a k 71*walk k 32 [43, 47, 7, 17, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_350 (a k) (relation_zero k) (e k 32)
lemma arrow_span_515 (b : Fin 75) : a k b*normalRep k 515 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_515_69 k]
      exact normal_mem k 632
    · rw [extension_515_70 k]
      exact normal_mem k 633
    · rw [extension_515_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 515=0 from arrow_incompatible k b 32 43 [43, 47, 7, 17, 21] (normal_endpoints 515) h]
    exact Submodule.zero_mem _
lemma extension_516_69 : a k 69*normalRep k 516=0 := by
  change a k 69*walk k 32 [43, 48, 51, 64, 36]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_371 (a k) (relation_zero k) (e k 32)
lemma extension_516_70 : a k 70*normalRep k 516=normalRep k 633 := by
  change a k 70*walk k 32 [43, 48, 51, 64, 36]=walk k 32 [43, 47, 7, 17, 21, 70]
  rw [← walk_snoc]
  exact Universal.mul_reduced_384 (a k) (relation_zero k) (e k 32)
lemma extension_516_71 : a k 71*normalRep k 516=normalRep k 634 := by
  exact (walk_snoc k 32 [43, 48, 51, 64, 36] 71).symm
lemma arrow_span_516 (b : Fin 75) : a k b*normalRep k 516 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_516_69 k]
      exact Submodule.zero_mem _
    · rw [extension_516_70 k]
      exact normal_mem k 633
    · rw [extension_516_71 k]
      exact normal_mem k 634
  · rw [show a k b*normalRep k 516=0 from arrow_incompatible k b 32 43 [43, 48, 51, 64, 36] (normal_endpoints 516) h]
    exact Submodule.zero_mem _
lemma extension_517_30 : a k 30*normalRep k 517=normalRep k 635 := by
  exact (walk_snoc k 32 [44, 57, 5, 63, 20] 30).symm
lemma extension_517_31 : a k 31*normalRep k 517=0 := by
  change a k 31*walk k 32 [44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_348 (a k) (relation_zero k) (e k 32)
lemma arrow_span_517 (b : Fin 75) : a k b*normalRep k 517 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_517_30 k]
      exact normal_mem k 635
    · rw [extension_517_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 517=0 from arrow_incompatible k b 32 24 [44, 57, 5, 63, 20] (normal_endpoints 517) h]
    exact Submodule.zero_mem _
lemma extension_518_69 : a k 69*normalRep k 518=normalRep k 636 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21] 69).symm
lemma extension_518_70 : a k 70*normalRep k 518=normalRep k 637 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21] 70).symm
lemma extension_518_71 : a k 71*normalRep k 518=0 := by
  change a k 71*walk k 33 [45, 6, 7, 17, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_351 (a k) (relation_zero k) (e k 33)
lemma arrow_span_518 (b : Fin 75) : a k b*normalRep k 518 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_518_69 k]
      exact normal_mem k 636
    · rw [extension_518_70 k]
      exact normal_mem k 637
    · rw [extension_518_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 518=0 from arrow_incompatible k b 33 43 [45, 6, 7, 17, 21] (normal_endpoints 518) h]
    exact Submodule.zero_mem _
lemma extension_519_69 : a k 69*normalRep k 519=0 := by
  change a k 69*walk k 33 [46, 48, 51, 64, 36]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_372 (a k) (relation_zero k) (e k 33)
lemma extension_519_70 : a k 70*normalRep k 519=normalRep k 637 := by
  change a k 70*walk k 33 [46, 48, 51, 64, 36]=walk k 33 [45, 6, 7, 17, 21, 70]
  rw [← walk_snoc]
  exact Universal.mul_reduced_385 (a k) (relation_zero k) (e k 33)
lemma extension_519_71 : a k 71*normalRep k 519=normalRep k 638 := by
  exact (walk_snoc k 33 [46, 48, 51, 64, 36] 71).symm
lemma arrow_span_519 (b : Fin 75) : a k b*normalRep k 519 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_519_69 k]
      exact Submodule.zero_mem _
    · rw [extension_519_70 k]
      exact normal_mem k 637
    · rw [extension_519_71 k]
      exact normal_mem k 638
  · rw [show a k b*normalRep k 519=0 from arrow_incompatible k b 33 43 [46, 48, 51, 64, 36] (normal_endpoints 519) h]
    exact Submodule.zero_mem _
lemma extension_520_8 : a k 8*normalRep k 520=normalRep k 639 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69] 8).symm
lemma arrow_span_520 (b : Fin 75) : a k b*normalRep k 520 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_520_8 k]
      exact normal_mem k 639
  · rw [show a k b*normalRep k 520=0 from arrow_incompatible k b 34 8 [47, 7, 17, 21, 69] (normal_endpoints 520) h]
    exact Submodule.zero_mem _
lemma extension_521_22 : a k 22*normalRep k 521=normalRep k 640 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 70] 22).symm
lemma extension_521_23 : a k 23*normalRep k 521=(-normalRep k 639) := by
  change a k 23*walk k 34 [47, 7, 17, 21, 70]=(-walk k 34 [47, 7, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_413 (a k) (relation_zero k) (e k 34)
lemma arrow_span_521 (b : Fin 75) : a k b*normalRep k 521 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_521_22 k]
      exact normal_mem k 640
    · rw [extension_521_23 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 639)
  · rw [show a k b*normalRep k 521=0 from arrow_incompatible k b 34 19 [47, 7, 17, 21, 70] (normal_endpoints 521) h]
    exact Submodule.zero_mem _
lemma extension_522_72 : a k 72*normalRep k 522=normalRep k 641 := by
  exact (walk_snoc k 34 [48, 51, 64, 36, 71] 72).symm
lemma extension_522_73 : a k 73*normalRep k 522=(-normalRep k 639) := by
  change a k 73*walk k 34 [48, 51, 64, 36, 71]=(-walk k 34 [47, 7, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_414 (a k) (relation_zero k) (e k 34)
lemma arrow_span_522 (b : Fin 75) : a k b*normalRep k 522 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_522_72 k]
      exact normal_mem k 641
    · rw [extension_522_73 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 639)
  · rw [show a k b*normalRep k 522=0 from arrow_incompatible k b 34 44 [48, 51, 64, 36, 71] (normal_endpoints 522) h]
    exact Submodule.zero_mem _
lemma extension_523_18 : a k 18*normalRep k 523=normalRep k 642 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24] 18).symm
lemma extension_523_19 : a k 19*normalRep k 523=normalRep k 643 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24] 19).symm
lemma arrow_span_523 (b : Fin 75) : a k b*normalRep k 523 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_523_18 k]
      exact normal_mem k 642
    · rw [extension_523_19 k]
      exact normal_mem k 643
  · rw [show a k b*normalRep k 523=0 from arrow_incompatible k b 35 17 [49, 69, 8, 66, 24] (normal_endpoints 523) h]
    exact Submodule.zero_mem _
lemma extension_524_60 : a k 60*normalRep k 524=normalRep k 644 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 25] 60).symm
lemma extension_524_61 : a k 61*normalRep k 524=0 := by
  change a k 61*walk k 35 [49, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_357 (a k) (relation_zero k) (e k 35)
lemma extension_524_62 : a k 62*normalRep k 524=normalRep k 643 := by
  change a k 62*walk k 35 [49, 69, 8, 66, 25]=walk k 35 [49, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_360 (a k) (relation_zero k) (e k 35)
lemma arrow_span_524 (b : Fin 75) : a k b*normalRep k 524 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_524_60 k]
      exact normal_mem k 644
    · rw [extension_524_61 k]
      exact Submodule.zero_mem _
    · rw [extension_524_62 k]
      exact normal_mem k 643
  · rw [show a k b*normalRep k 524=0 from arrow_incompatible k b 35 40 [49, 69, 8, 66, 25] (normal_endpoints 524) h]
    exact Submodule.zero_mem _
lemma extension_525_14 : a k 14*normalRep k 525=normalRep k 642 := by
  change a k 14*walk k 35 [49, 71, 72, 38, 28]=walk k 35 [49, 69, 8, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_364 (a k) (relation_zero k) (e k 35)
lemma arrow_span_525 (b : Fin 75) : a k b*normalRep k 525 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_525_14 k]
      exact normal_mem k 642
  · rw [show a k b*normalRep k 525=0 from arrow_incompatible k b 35 14 [49, 71, 72, 38, 28] (normal_endpoints 525) h]
    exact Submodule.zero_mem _
lemma extension_526_66 : a k 66*normalRep k 526=normalRep k 645 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8] 66).symm
lemma extension_526_67 : a k 67*normalRep k 526=0 := by
  change a k 67*walk k 36 [50, 17, 21, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_333 (a k) (relation_zero k) (e k 36)
lemma extension_526_68 : a k 68*normalRep k 526=normalRep k 646 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8] 68).symm
lemma arrow_span_526 (b : Fin 75) : a k b*normalRep k 526 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_526_66 k]
      exact normal_mem k 645
    · rw [extension_526_67 k]
      exact Submodule.zero_mem _
    · rw [extension_526_68 k]
      exact normal_mem k 646
  · rw [show a k b*normalRep k 526=0 from arrow_incompatible k b 36 42 [50, 17, 21, 69, 8] (normal_endpoints 526) h]
    exact Submodule.zero_mem _
lemma extension_527_3 : a k 3*normalRep k 527=normalRep k 646 := by
  change a k 3*walk k 36 [50, 17, 21, 70, 22]=walk k 36 [50, 17, 21, 69, 8, 68]
  rw [← walk_snoc]
  exact Universal.mul_reduced_354 (a k) (relation_zero k) (e k 36)
lemma arrow_span_527 (b : Fin 75) : a k b*normalRep k 527 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_527_3 k]
      exact normal_mem k 646
  · rw [show a k b*normalRep k 527=0 from arrow_incompatible k b 36 3 [50, 17, 21, 70, 22] (normal_endpoints 527) h]
    exact Submodule.zero_mem _
lemma extension_528_37 : a k 37*normalRep k 528=(-normalRep k 645) := by
  change a k 37*walk k 36 [51, 64, 36, 71, 72]=(-walk k 36 [50, 17, 21, 69, 8, 66])
  rw [← walk_snoc]
  exact Universal.mul_reduced_419 (a k) (relation_zero k) (e k 36)
lemma extension_528_38 : a k 38*normalRep k 528=normalRep k 647 := by
  exact (walk_snoc k 36 [51, 64, 36, 71, 72] 38).symm
lemma arrow_span_528 (b : Fin 75) : a k b*normalRep k 528 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_528_37 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 645)
    · rw [extension_528_38 k]
      exact normal_mem k 647
  · rw [show a k b*normalRep k 528=0 from arrow_incompatible k b 36 29 [51, 64, 36, 71, 72] (normal_endpoints 528) h]
    exact Submodule.zero_mem _
lemma extension_529_17 : a k 17*normalRep k 529=normalRep k 648 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7] 17).symm
lemma arrow_span_529 (b : Fin 75) : a k b*normalRep k 529 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_529_17 k]
      exact normal_mem k 648
  · rw [show a k b*normalRep k 529=0 from arrow_incompatible k b 37 16 [52, 41, 43, 47, 7] (normal_endpoints 529) h]
    exact Submodule.zero_mem _
lemma extension_530_63 : a k 63*normalRep k 530=normalRep k 648 := by
  change a k 63*walk k 37 [52, 41, 43, 48, 51]=walk k 37 [52, 41, 43, 47, 7, 17]
  rw [← walk_snoc]
  exact Universal.mul_reduced_387 (a k) (relation_zero k) (e k 37)
lemma extension_530_64 : a k 64*normalRep k 530=normalRep k 649 := by
  exact (walk_snoc k 37 [52, 41, 43, 48, 51] 64).symm
lemma extension_530_65 : a k 65*normalRep k 530=normalRep k 650 := by
  exact (walk_snoc k 37 [52, 41, 43, 48, 51] 65).symm
lemma arrow_span_530 (b : Fin 75) : a k b*normalRep k 530 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_530_63 k]
      exact normal_mem k 648
    · rw [extension_530_64 k]
      exact normal_mem k 649
    · rw [extension_530_65 k]
      exact normal_mem k 650
  · rw [show a k b*normalRep k 530=0 from arrow_incompatible k b 37 41 [52, 41, 43, 48, 51] (normal_endpoints 530) h]
    exact Submodule.zero_mem _
lemma extension_531_63 : a k 63*normalRep k 531=normalRep k 651 := by
  exact (walk_snoc k 37 [52, 41, 44, 57, 5] 63).symm
lemma extension_531_64 : a k 64*normalRep k 531=0 := by
  change a k 64*walk k 37 [52, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_316 (a k) (relation_zero k) (e k 37)
lemma extension_531_65 : a k 65*normalRep k 531=0 := by
  change a k 65*walk k 37 [52, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_329 (a k) (relation_zero k) (e k 37)
lemma arrow_span_531 (b : Fin 75) : a k b*normalRep k 531 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_531_63 k]
      exact normal_mem k 651
    · rw [extension_531_64 k]
      exact Submodule.zero_mem _
    · rw [extension_531_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 531=0 from arrow_incompatible k b 37 41 [52, 41, 44, 57, 5] (normal_endpoints 531) h]
    exact Submodule.zero_mem _
lemma extension_532_13 : a k 13*normalRep k 532=normalRep k 650 := by
  change a k 13*walk k 37 [52, 41, 44, 58, 33]=walk k 37 [52, 41, 43, 48, 51, 65]
  rw [← walk_snoc]
  exact Universal.mul_reduced_368 (a k) (relation_zero k) (e k 37)
lemma arrow_span_532 (b : Fin 75) : a k b*normalRep k 532 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_532_13 k]
      exact normal_mem k 650
  · rw [show a k b*normalRep k 532=0 from arrow_incompatible k b 37 13 [52, 41, 44, 58, 33] (normal_endpoints 532) h]
    exact Submodule.zero_mem _
lemma extension_533_20 : a k 20*normalRep k 533=normalRep k 652 := by
  exact (walk_snoc k 38 [54, 15, 1, 34, 63] 20).symm
lemma extension_533_21 : a k 21*normalRep k 533=0 := by
  change a k 21*walk k 38 [54, 15, 1, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_406 (a k) (relation_zero k) (e k 38)
lemma arrow_span_533 (b : Fin 75) : a k b*normalRep k 533 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_533_20 k]
      exact normal_mem k 652
    · rw [extension_533_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 533=0 from arrow_incompatible k b 38 18 [54, 15, 1, 34, 63] (normal_endpoints 533) h]
    exact Submodule.zero_mem _
lemma extension_534_49 : a k 49*normalRep k 534=normalRep k 653 := by
  exact (walk_snoc k 38 [55, 27, 58, 33, 13] 49).symm
lemma arrow_span_534 (b : Fin 75) : a k b*normalRep k 534 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_534_49 k]
      exact normal_mem k 653
  · rw [show a k b*normalRep k 534=0 from arrow_incompatible k b 38 35 [55, 27, 58, 33, 13] (normal_endpoints 534) h]
    exact Submodule.zero_mem _
lemma extension_535_20 : a k 20*normalRep k 535=0 := by
  change a k 20*walk k 38 [55, 27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_344 (a k) (relation_zero k) (e k 38)
lemma extension_535_21 : a k 21*normalRep k 535=normalRep k 654 := by
  exact (walk_snoc k 38 [55, 27, 58, 34, 63] 21).symm
lemma arrow_span_535 (b : Fin 75) : a k b*normalRep k 535 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_535_20 k]
      exact Submodule.zero_mem _
    · rw [extension_535_21 k]
      exact normal_mem k 654
  · rw [show a k b*normalRep k 535=0 from arrow_incompatible k b 38 18 [55, 27, 58, 34, 63] (normal_endpoints 535) h]
    exact Submodule.zero_mem _
lemma extension_536_36 : a k 36*normalRep k 536=normalRep k 654 + normalRep k 653 := by
  change a k 36*walk k 38 [55, 27, 58, 34, 64]=walk k 38 [55, 27, 58, 34, 63, 21] + walk k 38 [55, 27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_407 (a k) (relation_zero k) (e k 38)
lemma arrow_span_536 (b : Fin 75) : a k b*normalRep k 536 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_536_36 k]
      exact (normalSpan k).add_mem (normal_mem k 654) (normal_mem k 653)
  · rw [show a k b*normalRep k 536=0 from arrow_incompatible k b 38 28 [55, 27, 58, 34, 64] (normal_endpoints 536) h]
    exact Submodule.zero_mem _
lemma extension_537_2 : a k 2*normalRep k 537=normalRep k 655 := by
  exact (walk_snoc k 39 [57, 5, 63, 20, 30] 2).symm
lemma arrow_span_537 (b : Fin 75) : a k b*normalRep k 537 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_537_2 k]
      exact normal_mem k 655
  · rw [show a k b*normalRep k 537=0 from arrow_incompatible k b 39 2 [57, 5, 63, 20, 30] (normal_endpoints 537) h]
    exact Submodule.zero_mem _
lemma extension_538_8 : a k 8*normalRep k 538=normalRep k 656 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 69] 8).symm
lemma arrow_span_538 (b : Fin 75) : a k b*normalRep k 538 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_538_8 k]
      exact normal_mem k 656
  · rw [show a k b*normalRep k 538=0 from arrow_incompatible k b 39 8 [58, 33, 13, 49, 69] (normal_endpoints 538) h]
    exact Submodule.zero_mem _
lemma extension_539_72 : a k 72*normalRep k 539=normalRep k 657 := by
  exact (walk_snoc k 39 [58, 33, 13, 49, 71] 72).symm
lemma extension_539_73 : a k 73*normalRep k 539=normalRep k 656 := by
  change a k 73*walk k 39 [58, 33, 13, 49, 71]=walk k 39 [58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_415 (a k) (relation_zero k) (e k 39)
lemma arrow_span_539 (b : Fin 75) : a k b*normalRep k 539 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_539_72 k]
      exact normal_mem k 657
    · rw [extension_539_73 k]
      exact normal_mem k 656
  · rw [show a k b*normalRep k 539=0 from arrow_incompatible k b 39 44 [58, 33, 13, 49, 71] (normal_endpoints 539) h]
    exact Submodule.zero_mem _
lemma extension_540_22 : a k 22*normalRep k 540=normalRep k 658 := by
  exact (walk_snoc k 39 [58, 34, 63, 21, 70] 22).symm
lemma extension_540_23 : a k 23*normalRep k 540=normalRep k 656 := by
  change a k 23*walk k 39 [58, 34, 63, 21, 70]=walk k 39 [58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_416 (a k) (relation_zero k) (e k 39)
lemma arrow_span_540 (b : Fin 75) : a k b*normalRep k 540 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_540_22 k]
      exact normal_mem k 658
    · rw [extension_540_23 k]
      exact normal_mem k 656
  · rw [show a k b*normalRep k 540=0 from arrow_incompatible k b 39 19 [58, 34, 63, 21, 70] (normal_endpoints 540) h]
    exact Submodule.zero_mem _
lemma extension_541_33 : a k 33*normalRep k 541=0 := by
  change a k 33*walk k 40 [60, 4, 54, 15, 1]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_314 (a k) (relation_zero k) (e k 40)
lemma extension_541_34 : a k 34*normalRep k 541=normalRep k 659 := by
  exact (walk_snoc k 40 [60, 4, 54, 15, 1] 34).symm
lemma arrow_span_541 (b : Fin 75) : a k b*normalRep k 541 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_541_33 k]
      exact Submodule.zero_mem _
    · rw [extension_541_34 k]
      exact normal_mem k 659
  · rw [show a k b*normalRep k 541=0 from arrow_incompatible k b 40 26 [60, 4, 54, 15, 1] (normal_endpoints 541) h]
    exact Submodule.zero_mem _
lemma extension_542_5 : a k 5*normalRep k 542=normalRep k 659 := by
  change a k 5*walk k 40 [60, 4, 54, 16, 57]=walk k 40 [60, 4, 54, 15, 1, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_399 (a k) (relation_zero k) (e k 40)
lemma arrow_span_542 (b : Fin 75) : a k b*normalRep k 542 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_542_5 k]
      exact normal_mem k 659
  · rw [show a k b*normalRep k 542=0 from arrow_incompatible k b 40 5 [60, 4, 54, 16, 57] (normal_endpoints 542) h]
    exact Submodule.zero_mem _
lemma extension_543_33 : a k 33*normalRep k 543=normalRep k 660 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58] 33).symm
lemma extension_543_34 : a k 34*normalRep k 543=normalRep k 661 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 58] 34).symm
lemma arrow_span_543 (b : Fin 75) : a k b*normalRep k 543 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_543_33 k]
      exact normal_mem k 660
    · rw [extension_543_34 k]
      exact normal_mem k 661
  · rw [show a k b*normalRep k 543=0 from arrow_incompatible k b 40 26 [61, 35, 55, 27, 58] (normal_endpoints 543) h]
    exact Submodule.zero_mem _
lemma extension_544_50 : a k 50*normalRep k 544=normalRep k 662 := by
  exact (walk_snoc k 40 [61, 35, 55, 27, 59] 50).symm
lemma extension_544_51 : a k 51*normalRep k 544=normalRep k 661 := by
  change a k 51*walk k 40 [61, 35, 55, 27, 59]=walk k 40 [61, 35, 55, 27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_400 (a k) (relation_zero k) (e k 40)
lemma arrow_span_544 (b : Fin 75) : a k b*normalRep k 544 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_544_50 k]
      exact normal_mem k 662
    · rw [extension_544_51 k]
      exact normal_mem k 661
  · rw [show a k b*normalRep k 544=0 from arrow_incompatible k b 40 36 [61, 35, 55, 27, 59] (normal_endpoints 544) h]
    exact Submodule.zero_mem _
lemma extension_545_7 : a k 7*normalRep k 545=normalRep k 662 := by
  change a k 7*walk k 40 [61, 35, 56, 43, 47]=walk k 40 [61, 35, 55, 27, 59, 50]
  rw [← walk_snoc]
  exact Universal.mul_reduced_382 (a k) (relation_zero k) (e k 40)
lemma arrow_span_545 (b : Fin 75) : a k b*normalRep k 545 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_545_7 k]
      exact normal_mem k 662
  · rw [show a k b*normalRep k 545=0 from arrow_incompatible k b 40 7 [61, 35, 56, 43, 47] (normal_endpoints 545) h]
    exact Submodule.zero_mem _
lemma arrow_span_546 (b : Fin 75) : a k b*normalRep k 546 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 546=0 from arrow_incompatible k b 41 46 [63, 20, 30, 2, 0] (normal_endpoints 546) h]
    exact Submodule.zero_mem _
lemma extension_547_24 : a k 24*normalRep k 547=normalRep k 663 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66] 24).symm
lemma extension_547_25 : a k 25*normalRep k 547=normalRep k 664 := by
  exact (walk_snoc k 41 [63, 21, 69, 8, 66] 25).symm
lemma arrow_span_547 (b : Fin 75) : a k b*normalRep k 547 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_547_24 k]
      exact normal_mem k 663
    · rw [extension_547_25 k]
      exact normal_mem k 664
  · rw [show a k b*normalRep k 547=0 from arrow_incompatible k b 41 20 [63, 21, 69, 8, 66] (normal_endpoints 547) h]
    exact Submodule.zero_mem _
lemma extension_548_39 : a k 39*normalRep k 548=0 := by
  change a k 39*walk k 41 [63, 21, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_318 (a k) (relation_zero k) (e k 41)
lemma extension_548_40 : a k 40*normalRep k 548=(-normalRep k 664) := by
  change a k 40*walk k 41 [63, 21, 69, 8, 68]=(-walk k 41 [63, 21, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_411 (a k) (relation_zero k) (e k 41)
lemma arrow_span_548 (b : Fin 75) : a k b*normalRep k 548 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_548_39 k]
      exact Submodule.zero_mem _
    · rw [extension_548_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 664)
  · rw [show a k b*normalRep k 548=0 from arrow_incompatible k b 41 30 [63, 21, 69, 8, 68] (normal_endpoints 548) h]
    exact Submodule.zero_mem _
lemma extension_549_28 : a k 28*normalRep k 549=normalRep k 665 := by
  exact (walk_snoc k 41 [64, 36, 71, 72, 38] 28).symm
lemma extension_549_29 : a k 29*normalRep k 549=(-normalRep k 663) := by
  change a k 29*walk k 41 [64, 36, 71, 72, 38]=(-walk k 41 [63, 21, 69, 8, 66, 24])
  rw [← walk_snoc]
  exact Universal.mul_reduced_374 (a k) (relation_zero k) (e k 41)
lemma arrow_span_549 (b : Fin 75) : a k b*normalRep k 549 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_549_28 k]
      exact normal_mem k 665
    · rw [extension_549_29 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 663)
  · rw [show a k b*normalRep k 549=0 from arrow_incompatible k b 41 23 [64, 36, 71, 72, 38] (normal_endpoints 549) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
