import N6NormalData
import N6Reduced5
import N6Reduced6
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_450_15 : a k 15*normalRep k 450=normalRep k 567 := by
  exact (walk_snoc k 3 [3, 40, 60, 4, 54] 15).symm
lemma extension_450_16 : a k 16*normalRep k 450=normalRep k 568 := by
  exact (walk_snoc k 3 [3, 40, 60, 4, 54] 16).symm
lemma arrow_span_450 (b : Fin 75) : a k b*normalRep k 450 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_450_15 k]
      exact normal_mem k 567
    · rw [extension_450_16 k]
      exact normal_mem k 568
  · rw [show a k b*normalRep k 450=0 from arrow_incompatible k b 3 15 [3, 40, 60, 4, 54] (normal_endpoints 450) h]
    exact Submodule.zero_mem _
lemma extension_451_43 : a k 43*normalRep k 451=0 := by
  change a k 43*walk k 3 [3, 40, 60, 4, 56]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_323 (a k) (relation_zero k) (e k 3)
lemma extension_451_44 : a k 44*normalRep k 451=normalRep k 568 := by
  change a k 44*walk k 3 [3, 40, 60, 4, 56]=walk k 3 [3, 40, 60, 4, 54, 16]
  rw [← walk_snoc]
  exact Universal.mul_reduced_392 (a k) (relation_zero k) (e k 3)
lemma arrow_span_451 (b : Fin 75) : a k b*normalRep k 451 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_451_43 k]
      exact Submodule.zero_mem _
    · rw [extension_451_44 k]
      exact normal_mem k 568
  · rw [show a k b*normalRep k 451=0 from arrow_incompatible k b 3 32 [3, 40, 60, 4, 56] (normal_endpoints 451) h]
    exact Submodule.zero_mem _
lemma extension_452_63 : a k 63*normalRep k 452=normalRep k 569 := by
  exact (walk_snoc k 4 [4, 54, 15, 1, 34] 63).symm
lemma extension_452_64 : a k 64*normalRep k 452=0 := by
  change a k 64*walk k 4 [4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_315 (a k) (relation_zero k) (e k 4)
lemma extension_452_65 : a k 65*normalRep k 452=0 := by
  change a k 65*walk k 4 [4, 54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_327 (a k) (relation_zero k) (e k 4)
lemma arrow_span_452 (b : Fin 75) : a k b*normalRep k 452 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_452_63 k]
      exact normal_mem k 569
    · rw [extension_452_64 k]
      exact Submodule.zero_mem _
    · rw [extension_452_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 452=0 from arrow_incompatible k b 4 41 [4, 54, 15, 1, 34] (normal_endpoints 452) h]
    exact Submodule.zero_mem _
lemma extension_453_0 : a k 0*normalRep k 453=normalRep k 570 := by
  exact (walk_snoc k 5 [5, 63, 20, 30, 2] 0).symm
lemma arrow_span_453 (b : Fin 75) : a k b*normalRep k 453 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_453_0 k]
      exact normal_mem k 570
  · rw [show a k b*normalRep k 453=0 from arrow_incompatible k b 5 0 [5, 63, 20, 30, 2] (normal_endpoints 453) h]
    exact Submodule.zero_mem _
lemma extension_454_8 : a k 8*normalRep k 454=normalRep k 571 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 69] 8).symm
lemma arrow_span_454 (b : Fin 75) : a k b*normalRep k 454 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_454_8 k]
      exact normal_mem k 571
  · rw [show a k b*normalRep k 454=0 from arrow_incompatible k b 6 8 [6, 7, 17, 21, 69] (normal_endpoints 454) h]
    exact Submodule.zero_mem _
lemma extension_455_22 : a k 22*normalRep k 455=normalRep k 572 := by
  exact (walk_snoc k 6 [6, 7, 17, 21, 70] 22).symm
lemma extension_455_23 : a k 23*normalRep k 455=(-normalRep k 571) := by
  change a k 23*walk k 6 [6, 7, 17, 21, 70]=(-walk k 6 [6, 7, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_412 (a k) (relation_zero k) (e k 6)
lemma arrow_span_455 (b : Fin 75) : a k b*normalRep k 455 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_455_22 k]
      exact normal_mem k 572
    · rw [extension_455_23 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 571)
  · rw [show a k b*normalRep k 455=0 from arrow_incompatible k b 6 19 [6, 7, 17, 21, 70] (normal_endpoints 455) h]
    exact Submodule.zero_mem _
lemma extension_456_66 : a k 66*normalRep k 456=normalRep k 573 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8] 66).symm
lemma extension_456_67 : a k 67*normalRep k 456=0 := by
  change a k 67*walk k 7 [7, 17, 21, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_331 (a k) (relation_zero k) (e k 7)
lemma extension_456_68 : a k 68*normalRep k 456=normalRep k 574 := by
  exact (walk_snoc k 7 [7, 17, 21, 69, 8] 68).symm
lemma arrow_span_456 (b : Fin 75) : a k b*normalRep k 456 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_456_66 k]
      exact normal_mem k 573
    · rw [extension_456_67 k]
      exact Submodule.zero_mem _
    · rw [extension_456_68 k]
      exact normal_mem k 574
  · rw [show a k b*normalRep k 456=0 from arrow_incompatible k b 7 42 [7, 17, 21, 69, 8] (normal_endpoints 456) h]
    exact Submodule.zero_mem _
lemma extension_457_3 : a k 3*normalRep k 457=normalRep k 574 := by
  change a k 3*walk k 7 [7, 17, 21, 70, 22]=walk k 7 [7, 17, 21, 69, 8, 68]
  rw [← walk_snoc]
  exact Universal.mul_reduced_352 (a k) (relation_zero k) (e k 7)
lemma arrow_span_457 (b : Fin 75) : a k b*normalRep k 457 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_457_3 k]
      exact normal_mem k 574
  · rw [show a k b*normalRep k 457=0 from arrow_incompatible k b 7 3 [7, 17, 21, 70, 22] (normal_endpoints 457) h]
    exact Submodule.zero_mem _
lemma extension_458_41 : a k 41*normalRep k 458=normalRep k 575 := by
  exact (walk_snoc k 8 [8, 66, 24, 18, 9] 41).symm
lemma extension_458_42 : a k 42*normalRep k 458=0 := by
  change a k 42*walk k 8 [8, 66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_335 (a k) (relation_zero k) (e k 8)
lemma arrow_span_458 (b : Fin 75) : a k b*normalRep k 458 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_458_41 k]
      exact normal_mem k 575
    · rw [extension_458_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 458=0 from arrow_incompatible k b 8 31 [8, 66, 24, 18, 9] (normal_endpoints 458) h]
    exact Submodule.zero_mem _
lemma extension_459_54 : a k 54*normalRep k 459=normalRep k 576 := by
  exact (walk_snoc k 8 [8, 66, 24, 19, 53] 54).symm
lemma extension_459_55 : a k 55*normalRep k 459=0 := by
  change a k 55*walk k 8 [8, 66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_320 (a k) (relation_zero k) (e k 8)
lemma extension_459_56 : a k 56*normalRep k 459=normalRep k 575 := by
  change a k 56*walk k 8 [8, 66, 24, 19, 53]=walk k 8 [8, 66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_388 (a k) (relation_zero k) (e k 8)
lemma arrow_span_459 (b : Fin 75) : a k b*normalRep k 459 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_459_54 k]
      exact normal_mem k 576
    · rw [extension_459_55 k]
      exact Submodule.zero_mem _
    · rw [extension_459_56 k]
      exact normal_mem k 575
  · rw [show a k b*normalRep k 459=0 from arrow_incompatible k b 8 38 [8, 66, 24, 19, 53] (normal_endpoints 459) h]
    exact Submodule.zero_mem _
lemma extension_460_63 : a k 63*normalRep k 460=normalRep k 577 := by
  exact (walk_snoc k 9 [9, 41, 44, 57, 5] 63).symm
lemma extension_460_64 : a k 64*normalRep k 460=0 := by
  change a k 64*walk k 9 [9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_326 (a k) (relation_zero k) (e k 9)
lemma extension_460_65 : a k 65*normalRep k 460=0 := by
  change a k 65*walk k 9 [9, 41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_328 (a k) (relation_zero k) (e k 9)
lemma arrow_span_460 (b : Fin 75) : a k b*normalRep k 460 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_460_63 k]
      exact normal_mem k 577
    · rw [extension_460_64 k]
      exact Submodule.zero_mem _
    · rw [extension_460_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 460=0 from arrow_incompatible k b 9 41 [9, 41, 44, 57, 5] (normal_endpoints 460) h]
    exact Submodule.zero_mem _
lemma extension_461_66 : a k 66*normalRep k 461=0 := by
  change a k 66*walk k 10 [10, 11, 26, 31, 73]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_417 (a k) (relation_zero k) (e k 10)
lemma extension_461_67 : a k 67*normalRep k 461=normalRep k 578 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73] 67).symm
lemma extension_461_68 : a k 68*normalRep k 461=normalRep k 579 := by
  exact (walk_snoc k 10 [10, 11, 26, 31, 73] 68).symm
lemma arrow_span_461 (b : Fin 75) : a k b*normalRep k 461 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_461_66 k]
      exact Submodule.zero_mem _
    · rw [extension_461_67 k]
      exact normal_mem k 578
    · rw [extension_461_68 k]
      exact normal_mem k 579
  · rw [show a k b*normalRep k 461=0 from arrow_incompatible k b 10 42 [10, 11, 26, 31, 73] (normal_endpoints 461) h]
    exact Submodule.zero_mem _
lemma extension_462_32 : a k 32*normalRep k 462=normalRep k 580 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 67] 32).symm
lemma arrow_span_462 (b : Fin 75) : a k b*normalRep k 462 ∈ normalSpan k := by
  by_cases h : arrowSource b=25
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [32] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_462_32 k]
      exact normal_mem k 580
  · rw [show a k b*normalRep k 462=0 from arrow_incompatible k b 11 25 [11, 26, 31, 73, 67] (normal_endpoints 462) h]
    exact Submodule.zero_mem _
lemma extension_463_39 : a k 39*normalRep k 463=normalRep k 581 := by
  exact (walk_snoc k 11 [11, 26, 31, 73, 68] 39).symm
lemma extension_463_40 : a k 40*normalRep k 463=normalRep k 580 := by
  change a k 40*walk k 11 [11, 26, 31, 73, 68]=walk k 11 [11, 26, 31, 73, 67, 32]
  rw [← walk_snoc]
  exact Universal.mul_reduced_408 (a k) (relation_zero k) (e k 11)
lemma arrow_span_463 (b : Fin 75) : a k b*normalRep k 463 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_463_39 k]
      exact normal_mem k 581
    · rw [extension_463_40 k]
      exact normal_mem k 580
  · rw [show a k b*normalRep k 463=0 from arrow_incompatible k b 11 30 [11, 26, 31, 73, 68] (normal_endpoints 463) h]
    exact Submodule.zero_mem _
lemma extension_464_33 : a k 33*normalRep k 464=normalRep k 582 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58] 33).symm
lemma extension_464_34 : a k 34*normalRep k 464=normalRep k 583 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 58] 34).symm
lemma arrow_span_464 (b : Fin 75) : a k b*normalRep k 464 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_464_33 k]
      exact normal_mem k 582
    · rw [extension_464_34 k]
      exact normal_mem k 583
  · rw [show a k b*normalRep k 464=0 from arrow_incompatible k b 12 26 [12, 35, 55, 27, 58] (normal_endpoints 464) h]
    exact Submodule.zero_mem _
lemma extension_465_50 : a k 50*normalRep k 465=normalRep k 584 := by
  exact (walk_snoc k 12 [12, 35, 55, 27, 59] 50).symm
lemma extension_465_51 : a k 51*normalRep k 465=normalRep k 583 := by
  change a k 51*walk k 12 [12, 35, 55, 27, 59]=walk k 12 [12, 35, 55, 27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_396 (a k) (relation_zero k) (e k 12)
lemma arrow_span_465 (b : Fin 75) : a k b*normalRep k 465 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_465_50 k]
      exact normal_mem k 584
    · rw [extension_465_51 k]
      exact normal_mem k 583
  · rw [show a k b*normalRep k 465=0 from arrow_incompatible k b 12 36 [12, 35, 55, 27, 59] (normal_endpoints 465) h]
    exact Submodule.zero_mem _
lemma extension_466_7 : a k 7*normalRep k 466=normalRep k 584 := by
  change a k 7*walk k 12 [12, 35, 56, 43, 47]=walk k 12 [12, 35, 55, 27, 59, 50]
  rw [← walk_snoc]
  exact Universal.mul_reduced_381 (a k) (relation_zero k) (e k 12)
lemma arrow_span_466 (b : Fin 75) : a k b*normalRep k 466 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_466_7 k]
      exact normal_mem k 584
  · rw [show a k b*normalRep k 466=0 from arrow_incompatible k b 12 7 [12, 35, 56, 43, 47] (normal_endpoints 466) h]
    exact Submodule.zero_mem _
lemma extension_467_24 : a k 24*normalRep k 467=normalRep k 585 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66] 24).symm
lemma extension_467_25 : a k 25*normalRep k 467=normalRep k 586 := by
  exact (walk_snoc k 13 [13, 49, 69, 8, 66] 25).symm
lemma arrow_span_467 (b : Fin 75) : a k b*normalRep k 467 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_467_24 k]
      exact normal_mem k 585
    · rw [extension_467_25 k]
      exact normal_mem k 586
  · rw [show a k b*normalRep k 467=0 from arrow_incompatible k b 13 20 [13, 49, 69, 8, 66] (normal_endpoints 467) h]
    exact Submodule.zero_mem _
lemma extension_468_39 : a k 39*normalRep k 468=0 := by
  change a k 39*walk k 13 [13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_330 (a k) (relation_zero k) (e k 13)
lemma extension_468_40 : a k 40*normalRep k 468=(-normalRep k 586) := by
  change a k 40*walk k 13 [13, 49, 69, 8, 68]=(-walk k 13 [13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_409 (a k) (relation_zero k) (e k 13)
lemma arrow_span_468 (b : Fin 75) : a k b*normalRep k 468 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_468_39 k]
      exact Submodule.zero_mem _
    · rw [extension_468_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 586)
  · rw [show a k b*normalRep k 468=0 from arrow_incompatible k b 13 30 [13, 49, 69, 8, 68] (normal_endpoints 468) h]
    exact Submodule.zero_mem _
lemma extension_469_28 : a k 28*normalRep k 469=normalRep k 587 := by
  exact (walk_snoc k 13 [13, 49, 71, 72, 38] 28).symm
lemma extension_469_29 : a k 29*normalRep k 469=normalRep k 585 := by
  change a k 29*walk k 13 [13, 49, 71, 72, 38]=walk k 13 [13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_373 (a k) (relation_zero k) (e k 13)
lemma arrow_span_469 (b : Fin 75) : a k b*normalRep k 469 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_469_28 k]
      exact normal_mem k 587
    · rw [extension_469_29 k]
      exact normal_mem k 585
  · rw [show a k b*normalRep k 469=0 from arrow_incompatible k b 13 23 [13, 49, 71, 72, 38] (normal_endpoints 469) h]
    exact Submodule.zero_mem _
lemma extension_470_5 : a k 5*normalRep k 470=normalRep k 588 := by
  exact (walk_snoc k 14 [14, 9, 41, 44, 57] 5).symm
lemma arrow_span_470 (b : Fin 75) : a k b*normalRep k 470 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_470_5 k]
      exact normal_mem k 588
  · rw [show a k b*normalRep k 470=0 from arrow_incompatible k b 14 5 [14, 9, 41, 44, 57] (normal_endpoints 470) h]
    exact Submodule.zero_mem _
lemma extension_471_33 : a k 33*normalRep k 471=0 := by
  change a k 33*walk k 14 [14, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_334 (a k) (relation_zero k) (e k 14)
lemma extension_471_34 : a k 34*normalRep k 471=normalRep k 588 := by
  change a k 34*walk k 14 [14, 9, 41, 44, 58]=walk k 14 [14, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_397 (a k) (relation_zero k) (e k 14)
lemma arrow_span_471 (b : Fin 75) : a k b*normalRep k 471 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_471_33 k]
      exact Submodule.zero_mem _
    · rw [extension_471_34 k]
      exact normal_mem k 588
  · rw [show a k b*normalRep k 471=0 from arrow_incompatible k b 14 26 [14, 9, 41, 44, 58] (normal_endpoints 471) h]
    exact Submodule.zero_mem _
lemma extension_472_30 : a k 30*normalRep k 472=normalRep k 589 := by
  exact (walk_snoc k 15 [15, 1, 34, 63, 20] 30).symm
lemma extension_472_31 : a k 31*normalRep k 472=0 := by
  change a k 31*walk k 15 [15, 1, 34, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_347 (a k) (relation_zero k) (e k 15)
lemma arrow_span_472 (b : Fin 75) : a k b*normalRep k 472 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_472_30 k]
      exact normal_mem k 589
    · rw [extension_472_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 472=0 from arrow_incompatible k b 15 24 [15, 1, 34, 63, 20] (normal_endpoints 472) h]
    exact Submodule.zero_mem _
lemma extension_473_24 : a k 24*normalRep k 473=normalRep k 590 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66] 24).symm
lemma extension_473_25 : a k 25*normalRep k 473=normalRep k 591 := by
  exact (walk_snoc k 16 [17, 21, 69, 8, 66] 25).symm
lemma arrow_span_473 (b : Fin 75) : a k b*normalRep k 473 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_473_24 k]
      exact normal_mem k 590
    · rw [extension_473_25 k]
      exact normal_mem k 591
  · rw [show a k b*normalRep k 473=0 from arrow_incompatible k b 16 20 [17, 21, 69, 8, 66] (normal_endpoints 473) h]
    exact Submodule.zero_mem _
lemma extension_474_39 : a k 39*normalRep k 474=0 := by
  change a k 39*walk k 16 [17, 21, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_317 (a k) (relation_zero k) (e k 16)
lemma extension_474_40 : a k 40*normalRep k 474=(-normalRep k 591) := by
  change a k 40*walk k 16 [17, 21, 69, 8, 68]=(-walk k 16 [17, 21, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_410 (a k) (relation_zero k) (e k 16)
lemma arrow_span_474 (b : Fin 75) : a k b*normalRep k 474 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_474_39 k]
      exact Submodule.zero_mem _
    · rw [extension_474_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 591)
  · rw [show a k b*normalRep k 474=0 from arrow_incompatible k b 16 30 [17, 21, 69, 8, 68] (normal_endpoints 474) h]
    exact Submodule.zero_mem _
lemma extension_475_5 : a k 5*normalRep k 475=normalRep k 592 := by
  exact (walk_snoc k 17 [18, 9, 41, 44, 57] 5).symm
lemma arrow_span_475 (b : Fin 75) : a k b*normalRep k 475 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_475_5 k]
      exact normal_mem k 592
  · rw [show a k b*normalRep k 475=0 from arrow_incompatible k b 17 5 [18, 9, 41, 44, 57] (normal_endpoints 475) h]
    exact Submodule.zero_mem _
lemma extension_476_33 : a k 33*normalRep k 476=0 := by
  change a k 33*walk k 17 [18, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_313 (a k) (relation_zero k) (e k 17)
lemma extension_476_34 : a k 34*normalRep k 476=normalRep k 592 := by
  change a k 34*walk k 17 [18, 9, 41, 44, 58]=walk k 17 [18, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_398 (a k) (relation_zero k) (e k 17)
lemma arrow_span_476 (b : Fin 75) : a k b*normalRep k 476 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_476_33 k]
      exact Submodule.zero_mem _
    · rw [extension_476_34 k]
      exact normal_mem k 592
  · rw [show a k b*normalRep k 476=0 from arrow_incompatible k b 17 26 [18, 9, 41, 44, 58] (normal_endpoints 476) h]
    exact Submodule.zero_mem _
lemma extension_477_18 : a k 18*normalRep k 477=normalRep k 593 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24] 18).symm
lemma extension_477_19 : a k 19*normalRep k 477=normalRep k 594 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 24] 19).symm
lemma arrow_span_477 (b : Fin 75) : a k b*normalRep k 477 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_477_18 k]
      exact normal_mem k 593
    · rw [extension_477_19 k]
      exact normal_mem k 594
  · rw [show a k b*normalRep k 477=0 from arrow_incompatible k b 18 17 [21, 69, 8, 66, 24] (normal_endpoints 477) h]
    exact Submodule.zero_mem _
lemma extension_478_60 : a k 60*normalRep k 478=normalRep k 595 := by
  exact (walk_snoc k 18 [21, 69, 8, 66, 25] 60).symm
lemma extension_478_61 : a k 61*normalRep k 478=0 := by
  change a k 61*walk k 18 [21, 69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_355 (a k) (relation_zero k) (e k 18)
lemma extension_478_62 : a k 62*normalRep k 478=normalRep k 594 := by
  change a k 62*walk k 18 [21, 69, 8, 66, 25]=walk k 18 [21, 69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_358 (a k) (relation_zero k) (e k 18)
lemma arrow_span_478 (b : Fin 75) : a k b*normalRep k 478 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_478_60 k]
      exact normal_mem k 595
    · rw [extension_478_61 k]
      exact Submodule.zero_mem _
    · rw [extension_478_62 k]
      exact normal_mem k 594
  · rw [show a k b*normalRep k 478=0 from arrow_incompatible k b 18 40 [21, 69, 8, 66, 25] (normal_endpoints 478) h]
    exact Submodule.zero_mem _
lemma extension_479_54 : a k 54*normalRep k 479=normalRep k 596 := by
  exact (walk_snoc k 19 [22, 3, 40, 60, 4] 54).symm
lemma extension_479_55 : a k 55*normalRep k 479=0 := by
  change a k 55*walk k 19 [22, 3, 40, 60, 4]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_321 (a k) (relation_zero k) (e k 19)
lemma extension_479_56 : a k 56*normalRep k 479=normalRep k 597 := by
  exact (walk_snoc k 19 [22, 3, 40, 60, 4] 56).symm
lemma arrow_span_479 (b : Fin 75) : a k b*normalRep k 479 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_479_54 k]
      exact normal_mem k 596
    · rw [extension_479_55 k]
      exact Submodule.zero_mem _
    · rw [extension_479_56 k]
      exact normal_mem k 597
  · rw [show a k b*normalRep k 479=0 from arrow_incompatible k b 19 38 [22, 3, 40, 60, 4] (normal_endpoints 479) h]
    exact Submodule.zero_mem _
lemma extension_480_41 : a k 41*normalRep k 480=normalRep k 597 := by
  change a k 41*walk k 19 [22, 3, 40, 62, 52]=walk k 19 [22, 3, 40, 60, 4, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_389 (a k) (relation_zero k) (e k 19)
lemma extension_480_42 : a k 42*normalRep k 480=0 := by
  change a k 42*walk k 19 [22, 3, 40, 62, 52]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_319 (a k) (relation_zero k) (e k 19)
lemma arrow_span_480 (b : Fin 75) : a k b*normalRep k 480 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_480_41 k]
      exact normal_mem k 597
    · rw [extension_480_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 480=0 from arrow_incompatible k b 19 31 [22, 3, 40, 62, 52] (normal_endpoints 480) h]
    exact Submodule.zero_mem _
lemma extension_481_57 : a k 57*normalRep k 481=normalRep k 598 := by
  exact (walk_snoc k 20 [24, 18, 9, 41, 44] 57).symm
lemma extension_481_58 : a k 58*normalRep k 481=normalRep k 599 := by
  exact (walk_snoc k 20 [24, 18, 9, 41, 44] 58).symm
lemma extension_481_59 : a k 59*normalRep k 481=0 := by
  change a k 59*walk k 20 [24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_340 (a k) (relation_zero k) (e k 20)
lemma arrow_span_481 (b : Fin 75) : a k b*normalRep k 481 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_481_57 k]
      exact normal_mem k 598
    · rw [extension_481_58 k]
      exact normal_mem k 599
    · rw [extension_481_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 481=0 from arrow_incompatible k b 20 39 [24, 18, 9, 41, 44] (normal_endpoints 481) h]
    exact Submodule.zero_mem _
lemma extension_482_1 : a k 1*normalRep k 482=normalRep k 599 := by
  change a k 1*walk k 20 [24, 19, 53, 54, 15]=walk k 20 [24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_337 (a k) (relation_zero k) (e k 20)
lemma arrow_span_482 (b : Fin 75) : a k b*normalRep k 482 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_482_1 k]
      exact normal_mem k 599
  · rw [show a k b*normalRep k 482=0 from arrow_incompatible k b 20 1 [24, 19, 53, 54, 15] (normal_endpoints 482) h]
    exact Submodule.zero_mem _
lemma extension_483_60 : a k 60*normalRep k 483=0 := by
  change a k 60*walk k 21 [26, 31, 73, 67, 32]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_366 (a k) (relation_zero k) (e k 21)
lemma extension_483_61 : a k 61*normalRep k 483=normalRep k 600 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32] 61).symm
lemma extension_483_62 : a k 62*normalRep k 483=normalRep k 601 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32] 62).symm
lemma arrow_span_483 (b : Fin 75) : a k b*normalRep k 483 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_483_60 k]
      exact Submodule.zero_mem _
    · rw [extension_483_61 k]
      exact normal_mem k 600
    · rw [extension_483_62 k]
      exact normal_mem k 601
  · rw [show a k b*normalRep k 483=0 from arrow_incompatible k b 21 40 [26, 31, 73, 67, 32] (normal_endpoints 483) h]
    exact Submodule.zero_mem _
lemma extension_484_12 : a k 12*normalRep k 484=normalRep k 600 := by
  change a k 12*walk k 21 [26, 31, 73, 68, 39]=walk k 21 [26, 31, 73, 67, 32, 61]
  rw [← walk_snoc]
  exact Universal.mul_reduced_375 (a k) (relation_zero k) (e k 21)
lemma arrow_span_484 (b : Fin 75) : a k b*normalRep k 484 ∈ normalSpan k := by
  by_cases h : arrowSource b=12
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [12] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_484_12 k]
      exact normal_mem k 600
  · rw [show a k b*normalRep k 484=0 from arrow_incompatible k b 21 12 [26, 31, 73, 68, 39] (normal_endpoints 484) h]
    exact Submodule.zero_mem _
lemma extension_485_69 : a k 69*normalRep k 485=normalRep k 602 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49] 69).symm
lemma extension_485_70 : a k 70*normalRep k 485=0 := by
  change a k 70*walk k 22 [27, 58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_383 (a k) (relation_zero k) (e k 22)
lemma extension_485_71 : a k 71*normalRep k 485=normalRep k 603 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49] 71).symm
lemma arrow_span_485 (b : Fin 75) : a k b*normalRep k 485 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_485_69 k]
      exact normal_mem k 602
    · rw [extension_485_70 k]
      exact Submodule.zero_mem _
    · rw [extension_485_71 k]
      exact normal_mem k 603
  · rw [show a k b*normalRep k 485=0 from arrow_incompatible k b 22 43 [27, 58, 33, 13, 49] (normal_endpoints 485) h]
    exact Submodule.zero_mem _
lemma extension_486_69 : a k 69*normalRep k 486=(-normalRep k 602) := by
  change a k 69*walk k 22 [27, 58, 34, 63, 21]=(-walk k 22 [27, 58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_370 (a k) (relation_zero k) (e k 22)
lemma extension_486_70 : a k 70*normalRep k 486=normalRep k 604 := by
  exact (walk_snoc k 22 [27, 58, 34, 63, 21] 70).symm
lemma extension_486_71 : a k 71*normalRep k 486=0 := by
  change a k 71*walk k 22 [27, 58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_349 (a k) (relation_zero k) (e k 22)
lemma arrow_span_486 (b : Fin 75) : a k b*normalRep k 486 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_486_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 602)
    · rw [extension_486_70 k]
      exact normal_mem k 604
    · rw [extension_486_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 486=0 from arrow_incompatible k b 22 43 [27, 58, 34, 63, 21] (normal_endpoints 486) h]
    exact Submodule.zero_mem _
lemma extension_487_57 : a k 57*normalRep k 487=normalRep k 605 := by
  exact (walk_snoc k 23 [28, 14, 9, 41, 44] 57).symm
lemma extension_487_58 : a k 58*normalRep k 487=normalRep k 606 := by
  exact (walk_snoc k 23 [28, 14, 9, 41, 44] 58).symm
lemma extension_487_59 : a k 59*normalRep k 487=0 := by
  change a k 59*walk k 23 [28, 14, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_341 (a k) (relation_zero k) (e k 23)
lemma arrow_span_487 (b : Fin 75) : a k b*normalRep k 487 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_487_57 k]
      exact normal_mem k 605
    · rw [extension_487_58 k]
      exact normal_mem k 606
    · rw [extension_487_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 487=0 from arrow_incompatible k b 23 39 [28, 14, 9, 41, 44] (normal_endpoints 487) h]
    exact Submodule.zero_mem _
lemma extension_488_1 : a k 1*normalRep k 488=normalRep k 606 := by
  change a k 1*walk k 23 [29, 19, 53, 54, 15]=walk k 23 [28, 14, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_338 (a k) (relation_zero k) (e k 23)
lemma arrow_span_488 (b : Fin 75) : a k b*normalRep k 488 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_488_1 k]
      exact normal_mem k 606
  · rw [show a k b*normalRep k 488=0 from arrow_incompatible k b 23 1 [29, 19, 53, 54, 15] (normal_endpoints 488) h]
    exact Submodule.zero_mem _
lemma extension_489_35 : a k 35*normalRep k 489=normalRep k 607 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61] 35).symm
lemma arrow_span_489 (b : Fin 75) : a k b*normalRep k 489 ∈ normalSpan k := by
  by_cases h : arrowSource b=27
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [35] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_489_35 k]
      exact normal_mem k 607
  · rw [show a k b*normalRep k 489=0 from arrow_incompatible k b 24 27 [31, 73, 67, 32, 61] (normal_endpoints 489) h]
    exact Submodule.zero_mem _
lemma extension_490_52 : a k 52*normalRep k 490=normalRep k 608 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 62] 52).symm
lemma extension_490_53 : a k 53*normalRep k 490=normalRep k 607 := by
  change a k 53*walk k 24 [31, 73, 67, 32, 62]=walk k 24 [31, 73, 67, 32, 61, 35]
  rw [← walk_snoc]
  exact Universal.mul_reduced_401 (a k) (relation_zero k) (e k 24)
lemma arrow_span_490 (b : Fin 75) : a k b*normalRep k 490 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_490_52 k]
      exact normal_mem k 608
    · rw [extension_490_53 k]
      exact normal_mem k 607
  · rw [show a k b*normalRep k 490=0 from arrow_incompatible k b 24 37 [31, 73, 67, 32, 62] (normal_endpoints 490) h]
    exact Submodule.zero_mem _
lemma extension_491_57 : a k 57*normalRep k 491=0 := by
  change a k 57*walk k 25 [32, 61, 35, 55, 27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_361 (a k) (relation_zero k) (e k 25)
lemma extension_491_58 : a k 58*normalRep k 491=normalRep k 609 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27] 58).symm
lemma extension_491_59 : a k 59*normalRep k 491=normalRep k 610 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27] 59).symm
lemma arrow_span_491 (b : Fin 75) : a k b*normalRep k 491 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_491_57 k]
      exact Submodule.zero_mem _
    · rw [extension_491_58 k]
      exact normal_mem k 609
    · rw [extension_491_59 k]
      exact normal_mem k 610
  · rw [show a k b*normalRep k 491=0 from arrow_incompatible k b 25 39 [32, 61, 35, 55, 27] (normal_endpoints 491) h]
    exact Submodule.zero_mem _
lemma extension_492_47 : a k 47*normalRep k 492=normalRep k 611 := by
  exact (walk_snoc k 25 [32, 61, 35, 56, 43] 47).symm
lemma extension_492_48 : a k 48*normalRep k 492=normalRep k 610 := by
  change a k 48*walk k 25 [32, 61, 35, 56, 43]=walk k 25 [32, 61, 35, 55, 27, 59]
  rw [← walk_snoc]
  exact Universal.mul_reduced_377 (a k) (relation_zero k) (e k 25)
lemma arrow_span_492 (b : Fin 75) : a k b*normalRep k 492 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_492_47 k]
      exact normal_mem k 611
    · rw [extension_492_48 k]
      exact normal_mem k 610
  · rw [show a k b*normalRep k 492=0 from arrow_incompatible k b 25 34 [32, 61, 35, 56, 43] (normal_endpoints 492) h]
    exact Submodule.zero_mem _
lemma extension_493_6 : a k 6*normalRep k 493=normalRep k 611 := by
  change a k 6*walk k 25 [32, 62, 52, 42, 45]=walk k 25 [32, 61, 35, 56, 43, 47]
  rw [← walk_snoc]
  exact Universal.mul_reduced_379 (a k) (relation_zero k) (e k 25)
lemma arrow_span_493 (b : Fin 75) : a k b*normalRep k 493 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_493_6 k]
      exact normal_mem k 611
  · rw [show a k b*normalRep k 493=0 from arrow_incompatible k b 25 6 [32, 62, 52, 42, 45] (normal_endpoints 493) h]
    exact Submodule.zero_mem _
lemma extension_494_66 : a k 66*normalRep k 494=normalRep k 612 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8] 66).symm
lemma extension_494_67 : a k 67*normalRep k 494=0 := by
  change a k 67*walk k 26 [33, 13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_332 (a k) (relation_zero k) (e k 26)
lemma extension_494_68 : a k 68*normalRep k 494=normalRep k 613 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8] 68).symm
lemma arrow_span_494 (b : Fin 75) : a k b*normalRep k 494 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_494_66 k]
      exact normal_mem k 612
    · rw [extension_494_67 k]
      exact Submodule.zero_mem _
    · rw [extension_494_68 k]
      exact normal_mem k 613
  · rw [show a k b*normalRep k 494=0 from arrow_incompatible k b 26 42 [33, 13, 49, 69, 8] (normal_endpoints 494) h]
    exact Submodule.zero_mem _
lemma extension_495_37 : a k 37*normalRep k 495=normalRep k 612 := by
  change a k 37*walk k 26 [33, 13, 49, 71, 72]=walk k 26 [33, 13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_418 (a k) (relation_zero k) (e k 26)
lemma extension_495_38 : a k 38*normalRep k 495=normalRep k 614 := by
  exact (walk_snoc k 26 [33, 13, 49, 71, 72] 38).symm
lemma arrow_span_495 (b : Fin 75) : a k b*normalRep k 495 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_495_37 k]
      exact normal_mem k 612
    · rw [extension_495_38 k]
      exact normal_mem k 614
  · rw [show a k b*normalRep k 495=0 from arrow_incompatible k b 26 29 [33, 13, 49, 71, 72] (normal_endpoints 495) h]
    exact Submodule.zero_mem _
lemma extension_496_0 : a k 0*normalRep k 496=normalRep k 615 := by
  exact (walk_snoc k 26 [34, 63, 20, 30, 2] 0).symm
lemma arrow_span_496 (b : Fin 75) : a k b*normalRep k 496 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_496_0 k]
      exact normal_mem k 615
  · rw [show a k b*normalRep k 496=0 from arrow_incompatible k b 26 0 [34, 63, 20, 30, 2] (normal_endpoints 496) h]
    exact Submodule.zero_mem _
lemma extension_497_3 : a k 3*normalRep k 497=(-normalRep k 613) := by
  change a k 3*walk k 26 [34, 63, 21, 70, 22]=(-walk k 26 [33, 13, 49, 69, 8, 68])
  rw [← walk_snoc]
  exact Universal.mul_reduced_353 (a k) (relation_zero k) (e k 26)
lemma arrow_span_497 (b : Fin 75) : a k b*normalRep k 497 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_497_3 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 613)
  · rw [show a k b*normalRep k 497=0 from arrow_incompatible k b 26 3 [34, 63, 21, 70, 22] (normal_endpoints 497) h]
    exact Submodule.zero_mem _
lemma extension_498_13 : a k 13*normalRep k 498=normalRep k 616 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33] 13).symm
lemma arrow_span_498 (b : Fin 75) : a k b*normalRep k 498 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_498_13 k]
      exact normal_mem k 616
  · rw [show a k b*normalRep k 498=0 from arrow_incompatible k b 27 13 [35, 55, 27, 58, 33] (normal_endpoints 498) h]
    exact Submodule.zero_mem _
lemma extension_499_63 : a k 63*normalRep k 499=normalRep k 617 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 34] 63).symm
lemma extension_499_64 : a k 64*normalRep k 499=normalRep k 618 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 34] 64).symm
lemma extension_499_65 : a k 65*normalRep k 499=normalRep k 616 := by
  change a k 65*walk k 27 [35, 55, 27, 58, 34]=walk k 27 [35, 55, 27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_367 (a k) (relation_zero k) (e k 27)
lemma arrow_span_499 (b : Fin 75) : a k b*normalRep k 499 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_499_63 k]
      exact normal_mem k 617
    · rw [extension_499_64 k]
      exact normal_mem k 618
    · rw [extension_499_65 k]
      exact normal_mem k 616
  · rw [show a k b*normalRep k 499=0 from arrow_incompatible k b 27 41 [35, 55, 27, 58, 34] (normal_endpoints 499) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
