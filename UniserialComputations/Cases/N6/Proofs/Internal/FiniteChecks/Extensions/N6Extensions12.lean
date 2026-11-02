import N6NormalData
import N6Reduced7
import N6Reduced8
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_600_35 : a k 35*normalRep k 600=normalRep k 713 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 61] 35).symm
lemma arrow_span_600 (b : Fin 75) : a k b*normalRep k 600 ∈ normalSpan k := by
  by_cases h : arrowSource b=27
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [35] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_600_35 k]
      exact normal_mem k 713
  · rw [show a k b*normalRep k 600=0 from arrow_incompatible k b 21 27 [26, 31, 73, 67, 32, 61] (normal_endpoints 600) h]
    exact Submodule.zero_mem _
lemma extension_601_52 : a k 52*normalRep k 601=normalRep k 714 := by
  exact (walk_snoc k 21 [26, 31, 73, 67, 32, 62] 52).symm
lemma extension_601_53 : a k 53*normalRep k 601=normalRep k 713 := by
  change a k 53*walk k 21 [26, 31, 73, 67, 32, 62]=walk k 21 [26, 31, 73, 67, 32, 61, 35]
  rw [← walk_snoc]
  exact Universal.mul_reduced_500 (a k) (relation_zero k) (e k 21)
lemma arrow_span_601 (b : Fin 75) : a k b*normalRep k 601 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_601_52 k]
      exact normal_mem k 714
    · rw [extension_601_53 k]
      exact normal_mem k 713
  · rw [show a k b*normalRep k 601=0 from arrow_incompatible k b 21 37 [26, 31, 73, 67, 32, 62] (normal_endpoints 601) h]
    exact Submodule.zero_mem _
lemma extension_602_8 : a k 8*normalRep k 602=normalRep k 715 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 69] 8).symm
lemma arrow_span_602 (b : Fin 75) : a k b*normalRep k 602 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_602_8 k]
      exact normal_mem k 715
  · rw [show a k b*normalRep k 602=0 from arrow_incompatible k b 22 8 [27, 58, 33, 13, 49, 69] (normal_endpoints 602) h]
    exact Submodule.zero_mem _
lemma extension_603_72 : a k 72*normalRep k 603=normalRep k 716 := by
  exact (walk_snoc k 22 [27, 58, 33, 13, 49, 71] 72).symm
lemma extension_603_73 : a k 73*normalRep k 603=normalRep k 715 := by
  change a k 73*walk k 22 [27, 58, 33, 13, 49, 71]=walk k 22 [27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_512 (a k) (relation_zero k) (e k 22)
lemma arrow_span_603 (b : Fin 75) : a k b*normalRep k 603 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_603_72 k]
      exact normal_mem k 716
    · rw [extension_603_73 k]
      exact normal_mem k 715
  · rw [show a k b*normalRep k 603=0 from arrow_incompatible k b 22 44 [27, 58, 33, 13, 49, 71] (normal_endpoints 603) h]
    exact Submodule.zero_mem _
lemma extension_604_22 : a k 22*normalRep k 604=normalRep k 717 := by
  exact (walk_snoc k 22 [27, 58, 34, 63, 21, 70] 22).symm
lemma extension_604_23 : a k 23*normalRep k 604=normalRep k 715 := by
  change a k 23*walk k 22 [27, 58, 34, 63, 21, 70]=walk k 22 [27, 58, 33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_513 (a k) (relation_zero k) (e k 22)
lemma arrow_span_604 (b : Fin 75) : a k b*normalRep k 604 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_604_22 k]
      exact normal_mem k 717
    · rw [extension_604_23 k]
      exact normal_mem k 715
  · rw [show a k b*normalRep k 604=0 from arrow_incompatible k b 22 19 [27, 58, 34, 63, 21, 70] (normal_endpoints 604) h]
    exact Submodule.zero_mem _
lemma extension_605_5 : a k 5*normalRep k 605=normalRep k 718 := by
  exact (walk_snoc k 23 [28, 14, 9, 41, 44, 57] 5).symm
lemma arrow_span_605 (b : Fin 75) : a k b*normalRep k 605 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_605_5 k]
      exact normal_mem k 718
  · rw [show a k b*normalRep k 605=0 from arrow_incompatible k b 23 5 [28, 14, 9, 41, 44, 57] (normal_endpoints 605) h]
    exact Submodule.zero_mem _
lemma extension_606_33 : a k 33*normalRep k 606=0 := by
  change a k 33*walk k 23 [28, 14, 9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_421 (a k) (relation_zero k) (e k 23)
lemma extension_606_34 : a k 34*normalRep k 606=normalRep k 718 := by
  change a k 34*walk k 23 [28, 14, 9, 41, 44, 58]=walk k 23 [28, 14, 9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_495 (a k) (relation_zero k) (e k 23)
lemma arrow_span_606 (b : Fin 75) : a k b*normalRep k 606 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_606_33 k]
      exact Submodule.zero_mem _
    · rw [extension_606_34 k]
      exact normal_mem k 718
  · rw [show a k b*normalRep k 606=0 from arrow_incompatible k b 23 26 [28, 14, 9, 41, 44, 58] (normal_endpoints 606) h]
    exact Submodule.zero_mem _
lemma extension_607_54 : a k 54*normalRep k 607=0 := by
  change a k 54*walk k 24 [31, 73, 67, 32, 61, 35]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_472 (a k) (relation_zero k) (e k 24)
lemma extension_607_55 : a k 55*normalRep k 607=normalRep k 719 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35] 55).symm
lemma extension_607_56 : a k 56*normalRep k 607=normalRep k 720 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 61, 35] 56).symm
lemma arrow_span_607 (b : Fin 75) : a k b*normalRep k 607 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_607_54 k]
      exact Submodule.zero_mem _
    · rw [extension_607_55 k]
      exact normal_mem k 719
    · rw [extension_607_56 k]
      exact normal_mem k 720
  · rw [show a k b*normalRep k 607=0 from arrow_incompatible k b 24 38 [31, 73, 67, 32, 61, 35] (normal_endpoints 607) h]
    exact Submodule.zero_mem _
lemma extension_608_41 : a k 41*normalRep k 608=normalRep k 720 := by
  change a k 41*walk k 24 [31, 73, 67, 32, 62, 52]=walk k 24 [31, 73, 67, 32, 61, 35, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_487 (a k) (relation_zero k) (e k 24)
lemma extension_608_42 : a k 42*normalRep k 608=normalRep k 721 := by
  exact (walk_snoc k 24 [31, 73, 67, 32, 62, 52] 42).symm
lemma arrow_span_608 (b : Fin 75) : a k b*normalRep k 608 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_608_41 k]
      exact normal_mem k 720
    · rw [extension_608_42 k]
      exact normal_mem k 721
  · rw [show a k b*normalRep k 608=0 from arrow_incompatible k b 24 31 [31, 73, 67, 32, 62, 52] (normal_endpoints 608) h]
    exact Submodule.zero_mem _
lemma extension_609_33 : a k 33*normalRep k 609=normalRep k 722 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58] 33).symm
lemma extension_609_34 : a k 34*normalRep k 609=normalRep k 723 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 58] 34).symm
lemma arrow_span_609 (b : Fin 75) : a k b*normalRep k 609 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_609_33 k]
      exact normal_mem k 722
    · rw [extension_609_34 k]
      exact normal_mem k 723
  · rw [show a k b*normalRep k 609=0 from arrow_incompatible k b 25 26 [32, 61, 35, 55, 27, 58] (normal_endpoints 609) h]
    exact Submodule.zero_mem _
lemma extension_610_50 : a k 50*normalRep k 610=normalRep k 724 := by
  exact (walk_snoc k 25 [32, 61, 35, 55, 27, 59] 50).symm
lemma extension_610_51 : a k 51*normalRep k 610=normalRep k 723 := by
  change a k 51*walk k 25 [32, 61, 35, 55, 27, 59]=walk k 25 [32, 61, 35, 55, 27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_496 (a k) (relation_zero k) (e k 25)
lemma arrow_span_610 (b : Fin 75) : a k b*normalRep k 610 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_610_50 k]
      exact normal_mem k 724
    · rw [extension_610_51 k]
      exact normal_mem k 723
  · rw [show a k b*normalRep k 610=0 from arrow_incompatible k b 25 36 [32, 61, 35, 55, 27, 59] (normal_endpoints 610) h]
    exact Submodule.zero_mem _
lemma extension_611_7 : a k 7*normalRep k 611=normalRep k 724 := by
  change a k 7*walk k 25 [32, 61, 35, 56, 43, 47]=walk k 25 [32, 61, 35, 55, 27, 59, 50]
  rw [← walk_snoc]
  exact Universal.mul_reduced_481 (a k) (relation_zero k) (e k 25)
lemma arrow_span_611 (b : Fin 75) : a k b*normalRep k 611 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_611_7 k]
      exact normal_mem k 724
  · rw [show a k b*normalRep k 611=0 from arrow_incompatible k b 25 7 [32, 61, 35, 56, 43, 47] (normal_endpoints 611) h]
    exact Submodule.zero_mem _
lemma extension_612_24 : a k 24*normalRep k 612=normalRep k 725 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66] 24).symm
lemma extension_612_25 : a k 25*normalRep k 612=normalRep k 726 := by
  exact (walk_snoc k 26 [33, 13, 49, 69, 8, 66] 25).symm
lemma arrow_span_612 (b : Fin 75) : a k b*normalRep k 612 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_612_24 k]
      exact normal_mem k 725
    · rw [extension_612_25 k]
      exact normal_mem k 726
  · rw [show a k b*normalRep k 612=0 from arrow_incompatible k b 26 20 [33, 13, 49, 69, 8, 66] (normal_endpoints 612) h]
    exact Submodule.zero_mem _
lemma extension_613_39 : a k 39*normalRep k 613=0 := by
  change a k 39*walk k 26 [33, 13, 49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_426 (a k) (relation_zero k) (e k 26)
lemma extension_613_40 : a k 40*normalRep k 613=(-normalRep k 726) := by
  change a k 40*walk k 26 [33, 13, 49, 69, 8, 68]=(-walk k 26 [33, 13, 49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_510 (a k) (relation_zero k) (e k 26)
lemma arrow_span_613 (b : Fin 75) : a k b*normalRep k 613 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_613_39 k]
      exact Submodule.zero_mem _
    · rw [extension_613_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 726)
  · rw [show a k b*normalRep k 613=0 from arrow_incompatible k b 26 30 [33, 13, 49, 69, 8, 68] (normal_endpoints 613) h]
    exact Submodule.zero_mem _
lemma extension_614_28 : a k 28*normalRep k 614=normalRep k 727 := by
  exact (walk_snoc k 26 [33, 13, 49, 71, 72, 38] 28).symm
lemma extension_614_29 : a k 29*normalRep k 614=normalRep k 725 := by
  change a k 29*walk k 26 [33, 13, 49, 71, 72, 38]=walk k 26 [33, 13, 49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_475 (a k) (relation_zero k) (e k 26)
lemma arrow_span_614 (b : Fin 75) : a k b*normalRep k 614 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_614_28 k]
      exact normal_mem k 727
    · rw [extension_614_29 k]
      exact normal_mem k 725
  · rw [show a k b*normalRep k 614=0 from arrow_incompatible k b 26 23 [33, 13, 49, 71, 72, 38] (normal_endpoints 614) h]
    exact Submodule.zero_mem _
lemma arrow_span_615 (b : Fin 75) : a k b*normalRep k 615 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 615=0 from arrow_incompatible k b 26 46 [34, 63, 20, 30, 2, 0] (normal_endpoints 615) h]
    exact Submodule.zero_mem _
lemma extension_616_49 : a k 49*normalRep k 616=normalRep k 728 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 33, 13] 49).symm
lemma arrow_span_616 (b : Fin 75) : a k b*normalRep k 616 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_616_49 k]
      exact normal_mem k 728
  · rw [show a k b*normalRep k 616=0 from arrow_incompatible k b 27 35 [35, 55, 27, 58, 33, 13] (normal_endpoints 616) h]
    exact Submodule.zero_mem _
lemma extension_617_20 : a k 20*normalRep k 617=0 := by
  change a k 20*walk k 27 [35, 55, 27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_448 (a k) (relation_zero k) (e k 27)
lemma extension_617_21 : a k 21*normalRep k 617=normalRep k 729 := by
  exact (walk_snoc k 27 [35, 55, 27, 58, 34, 63] 21).symm
lemma arrow_span_617 (b : Fin 75) : a k b*normalRep k 617 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_617_20 k]
      exact Submodule.zero_mem _
    · rw [extension_617_21 k]
      exact normal_mem k 729
  · rw [show a k b*normalRep k 617=0 from arrow_incompatible k b 27 18 [35, 55, 27, 58, 34, 63] (normal_endpoints 617) h]
    exact Submodule.zero_mem _
lemma extension_618_36 : a k 36*normalRep k 618=normalRep k 729 + normalRep k 728 := by
  change a k 36*walk k 27 [35, 55, 27, 58, 34, 64]=walk k 27 [35, 55, 27, 58, 34, 63, 21] + walk k 27 [35, 55, 27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_505 (a k) (relation_zero k) (e k 27)
lemma arrow_span_618 (b : Fin 75) : a k b*normalRep k 618 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_618_36 k]
      exact (normalSpan k).add_mem (normal_mem k 729) (normal_mem k 728)
  · rw [show a k b*normalRep k 618=0 from arrow_incompatible k b 27 28 [35, 55, 27, 58, 34, 64] (normal_endpoints 618) h]
    exact Submodule.zero_mem _
lemma extension_619_4 : a k 4*normalRep k 619=normalRep k 730 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 60] 4).symm
lemma arrow_span_619 (b : Fin 75) : a k b*normalRep k 619 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_619_4 k]
      exact normal_mem k 730
  · rw [show a k b*normalRep k 619=0 from arrow_incompatible k b 28 4 [36, 70, 22, 3, 40, 60] (normal_endpoints 619) h]
    exact Submodule.zero_mem _
lemma extension_620_52 : a k 52*normalRep k 620=normalRep k 731 := by
  exact (walk_snoc k 28 [36, 70, 22, 3, 40, 62] 52).symm
lemma extension_620_53 : a k 53*normalRep k 620=normalRep k 730 := by
  change a k 53*walk k 28 [36, 70, 22, 3, 40, 62]=walk k 28 [36, 70, 22, 3, 40, 60, 4]
  rw [← walk_snoc]
  exact Universal.mul_reduced_501 (a k) (relation_zero k) (e k 28)
lemma arrow_span_620 (b : Fin 75) : a k b*normalRep k 620 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_620_52 k]
      exact normal_mem k 731
    · rw [extension_620_53 k]
      exact normal_mem k 730
  · rw [show a k b*normalRep k 620=0 from arrow_incompatible k b 28 37 [36, 70, 22, 3, 40, 62] (normal_endpoints 620) h]
    exact Submodule.zero_mem _
lemma extension_621_9 : a k 9*normalRep k 621=normalRep k 731 := by
  change a k 9*walk k 28 [36, 70, 23, 66, 24, 18]=walk k 28 [36, 70, 22, 3, 40, 62, 52]
  rw [← walk_snoc]
  exact Universal.mul_reduced_451 (a k) (relation_zero k) (e k 28)
lemma arrow_span_621 (b : Fin 75) : a k b*normalRep k 621 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_621_9 k]
      exact normal_mem k 731
  · rw [show a k b*normalRep k 621=0 from arrow_incompatible k b 28 9 [36, 70, 23, 66, 24, 18] (normal_endpoints 621) h]
    exact Submodule.zero_mem _
lemma extension_622_57 : a k 57*normalRep k 622=normalRep k 732 := by
  exact (walk_snoc k 29 [37, 24, 18, 9, 41, 44] 57).symm
lemma extension_622_58 : a k 58*normalRep k 622=normalRep k 733 := by
  exact (walk_snoc k 29 [37, 24, 18, 9, 41, 44] 58).symm
lemma extension_622_59 : a k 59*normalRep k 622=0 := by
  change a k 59*walk k 29 [37, 24, 18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_446 (a k) (relation_zero k) (e k 29)
lemma arrow_span_622 (b : Fin 75) : a k b*normalRep k 622 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_622_57 k]
      exact normal_mem k 732
    · rw [extension_622_58 k]
      exact normal_mem k 733
    · rw [extension_622_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 622=0 from arrow_incompatible k b 29 39 [37, 24, 18, 9, 41, 44] (normal_endpoints 622) h]
    exact Submodule.zero_mem _
lemma extension_623_1 : a k 1*normalRep k 623=normalRep k 733 := by
  change a k 1*walk k 29 [37, 24, 19, 53, 54, 15]=walk k 29 [37, 24, 18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_443 (a k) (relation_zero k) (e k 29)
lemma arrow_span_623 (b : Fin 75) : a k b*normalRep k 623 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_623_1 k]
      exact normal_mem k 733
  · rw [show a k b*normalRep k 623=0 from arrow_incompatible k b 29 1 [37, 24, 19, 53, 54, 15] (normal_endpoints 623) h]
    exact Submodule.zero_mem _
lemma extension_624_33 : a k 33*normalRep k 624=normalRep k 734 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58] 33).symm
lemma extension_624_34 : a k 34*normalRep k 624=normalRep k 735 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 58] 34).symm
lemma arrow_span_624 (b : Fin 75) : a k b*normalRep k 624 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_624_33 k]
      exact normal_mem k 734
    · rw [extension_624_34 k]
      exact normal_mem k 735
  · rw [show a k b*normalRep k 624=0 from arrow_incompatible k b 30 26 [39, 12, 35, 55, 27, 58] (normal_endpoints 624) h]
    exact Submodule.zero_mem _
lemma extension_625_50 : a k 50*normalRep k 625=normalRep k 736 := by
  exact (walk_snoc k 30 [39, 12, 35, 55, 27, 59] 50).symm
lemma extension_625_51 : a k 51*normalRep k 625=normalRep k 735 := by
  change a k 51*walk k 30 [39, 12, 35, 55, 27, 59]=walk k 30 [39, 12, 35, 55, 27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_497 (a k) (relation_zero k) (e k 30)
lemma arrow_span_625 (b : Fin 75) : a k b*normalRep k 625 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_625_50 k]
      exact normal_mem k 736
    · rw [extension_625_51 k]
      exact normal_mem k 735
  · rw [show a k b*normalRep k 625=0 from arrow_incompatible k b 30 36 [39, 12, 35, 55, 27, 59] (normal_endpoints 625) h]
    exact Submodule.zero_mem _
lemma extension_626_7 : a k 7*normalRep k 626=normalRep k 736 := by
  change a k 7*walk k 30 [39, 12, 35, 56, 43, 47]=walk k 30 [39, 12, 35, 55, 27, 59, 50]
  rw [← walk_snoc]
  exact Universal.mul_reduced_482 (a k) (relation_zero k) (e k 30)
lemma arrow_span_626 (b : Fin 75) : a k b*normalRep k 626 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_626_7 k]
      exact normal_mem k 736
  · rw [show a k b*normalRep k 626=0 from arrow_incompatible k b 30 7 [39, 12, 35, 56, 43, 47] (normal_endpoints 626) h]
    exact Submodule.zero_mem _
lemma extension_627_33 : a k 33*normalRep k 627=0 := by
  change a k 33*walk k 30 [40, 60, 4, 54, 15, 1]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_422 (a k) (relation_zero k) (e k 30)
lemma extension_627_34 : a k 34*normalRep k 627=normalRep k 737 := by
  exact (walk_snoc k 30 [40, 60, 4, 54, 15, 1] 34).symm
lemma arrow_span_627 (b : Fin 75) : a k b*normalRep k 627 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_627_33 k]
      exact Submodule.zero_mem _
    · rw [extension_627_34 k]
      exact normal_mem k 737
  · rw [show a k b*normalRep k 627=0 from arrow_incompatible k b 30 26 [40, 60, 4, 54, 15, 1] (normal_endpoints 627) h]
    exact Submodule.zero_mem _
lemma extension_628_5 : a k 5*normalRep k 628=normalRep k 737 := by
  change a k 5*walk k 30 [40, 60, 4, 54, 16, 57]=walk k 30 [40, 60, 4, 54, 15, 1, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_498 (a k) (relation_zero k) (e k 30)
lemma arrow_span_628 (b : Fin 75) : a k b*normalRep k 628 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_628_5 k]
      exact normal_mem k 737
  · rw [show a k b*normalRep k 628=0 from arrow_incompatible k b 30 5 [40, 60, 4, 54, 16, 57] (normal_endpoints 628) h]
    exact Submodule.zero_mem _
lemma extension_629_69 : a k 69*normalRep k 629=normalRep k 738 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21] 69).symm
lemma extension_629_70 : a k 70*normalRep k 629=normalRep k 739 := by
  exact (walk_snoc k 31 [41, 43, 47, 7, 17, 21] 70).symm
lemma extension_629_71 : a k 71*normalRep k 629=0 := by
  change a k 71*walk k 31 [41, 43, 47, 7, 17, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_455 (a k) (relation_zero k) (e k 31)
lemma arrow_span_629 (b : Fin 75) : a k b*normalRep k 629 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_629_69 k]
      exact normal_mem k 738
    · rw [extension_629_70 k]
      exact normal_mem k 739
    · rw [extension_629_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 629=0 from arrow_incompatible k b 31 43 [41, 43, 47, 7, 17, 21] (normal_endpoints 629) h]
    exact Submodule.zero_mem _
lemma extension_630_69 : a k 69*normalRep k 630=0 := by
  change a k 69*walk k 31 [41, 43, 48, 51, 64, 36]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_473 (a k) (relation_zero k) (e k 31)
lemma extension_630_70 : a k 70*normalRep k 630=normalRep k 739 := by
  change a k 70*walk k 31 [41, 43, 48, 51, 64, 36]=walk k 31 [41, 43, 47, 7, 17, 21, 70]
  rw [← walk_snoc]
  exact Universal.mul_reduced_483 (a k) (relation_zero k) (e k 31)
lemma extension_630_71 : a k 71*normalRep k 630=normalRep k 740 := by
  exact (walk_snoc k 31 [41, 43, 48, 51, 64, 36] 71).symm
lemma arrow_span_630 (b : Fin 75) : a k b*normalRep k 630 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_630_69 k]
      exact Submodule.zero_mem _
    · rw [extension_630_70 k]
      exact normal_mem k 739
    · rw [extension_630_71 k]
      exact normal_mem k 740
  · rw [show a k b*normalRep k 630=0 from arrow_incompatible k b 31 43 [41, 43, 48, 51, 64, 36] (normal_endpoints 630) h]
    exact Submodule.zero_mem _
lemma extension_631_30 : a k 30*normalRep k 631=normalRep k 741 := by
  exact (walk_snoc k 31 [41, 44, 57, 5, 63, 20] 30).symm
lemma extension_631_31 : a k 31*normalRep k 631=0 := by
  change a k 31*walk k 31 [41, 44, 57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_453 (a k) (relation_zero k) (e k 31)
lemma arrow_span_631 (b : Fin 75) : a k b*normalRep k 631 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_631_30 k]
      exact normal_mem k 741
    · rw [extension_631_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 631=0 from arrow_incompatible k b 31 24 [41, 44, 57, 5, 63, 20] (normal_endpoints 631) h]
    exact Submodule.zero_mem _
lemma extension_632_8 : a k 8*normalRep k 632=normalRep k 742 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 69] 8).symm
lemma arrow_span_632 (b : Fin 75) : a k b*normalRep k 632 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_632_8 k]
      exact normal_mem k 742
  · rw [show a k b*normalRep k 632=0 from arrow_incompatible k b 32 8 [43, 47, 7, 17, 21, 69] (normal_endpoints 632) h]
    exact Submodule.zero_mem _
lemma extension_633_22 : a k 22*normalRep k 633=normalRep k 743 := by
  exact (walk_snoc k 32 [43, 47, 7, 17, 21, 70] 22).symm
lemma extension_633_23 : a k 23*normalRep k 633=(-normalRep k 742) := by
  change a k 23*walk k 32 [43, 47, 7, 17, 21, 70]=(-walk k 32 [43, 47, 7, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_514 (a k) (relation_zero k) (e k 32)
lemma arrow_span_633 (b : Fin 75) : a k b*normalRep k 633 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_633_22 k]
      exact normal_mem k 743
    · rw [extension_633_23 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 742)
  · rw [show a k b*normalRep k 633=0 from arrow_incompatible k b 32 19 [43, 47, 7, 17, 21, 70] (normal_endpoints 633) h]
    exact Submodule.zero_mem _
lemma extension_634_72 : a k 72*normalRep k 634=normalRep k 744 := by
  exact (walk_snoc k 32 [43, 48, 51, 64, 36, 71] 72).symm
lemma extension_634_73 : a k 73*normalRep k 634=(-normalRep k 742) := by
  change a k 73*walk k 32 [43, 48, 51, 64, 36, 71]=(-walk k 32 [43, 47, 7, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_515 (a k) (relation_zero k) (e k 32)
lemma arrow_span_634 (b : Fin 75) : a k b*normalRep k 634 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_634_72 k]
      exact normal_mem k 744
    · rw [extension_634_73 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 742)
  · rw [show a k b*normalRep k 634=0 from arrow_incompatible k b 32 44 [43, 48, 51, 64, 36, 71] (normal_endpoints 634) h]
    exact Submodule.zero_mem _
lemma extension_635_2 : a k 2*normalRep k 635=normalRep k 745 := by
  exact (walk_snoc k 32 [44, 57, 5, 63, 20, 30] 2).symm
lemma arrow_span_635 (b : Fin 75) : a k b*normalRep k 635 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_635_2 k]
      exact normal_mem k 745
  · rw [show a k b*normalRep k 635=0 from arrow_incompatible k b 32 2 [44, 57, 5, 63, 20, 30] (normal_endpoints 635) h]
    exact Submodule.zero_mem _
lemma extension_636_8 : a k 8*normalRep k 636=normalRep k 746 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 69] 8).symm
lemma arrow_span_636 (b : Fin 75) : a k b*normalRep k 636 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_636_8 k]
      exact normal_mem k 746
  · rw [show a k b*normalRep k 636=0 from arrow_incompatible k b 33 8 [45, 6, 7, 17, 21, 69] (normal_endpoints 636) h]
    exact Submodule.zero_mem _
lemma extension_637_22 : a k 22*normalRep k 637=normalRep k 747 := by
  exact (walk_snoc k 33 [45, 6, 7, 17, 21, 70] 22).symm
lemma extension_637_23 : a k 23*normalRep k 637=(-normalRep k 746) := by
  change a k 23*walk k 33 [45, 6, 7, 17, 21, 70]=(-walk k 33 [45, 6, 7, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_516 (a k) (relation_zero k) (e k 33)
lemma arrow_span_637 (b : Fin 75) : a k b*normalRep k 637 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_637_22 k]
      exact normal_mem k 747
    · rw [extension_637_23 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 746)
  · rw [show a k b*normalRep k 637=0 from arrow_incompatible k b 33 19 [45, 6, 7, 17, 21, 70] (normal_endpoints 637) h]
    exact Submodule.zero_mem _
lemma extension_638_72 : a k 72*normalRep k 638=normalRep k 748 := by
  exact (walk_snoc k 33 [46, 48, 51, 64, 36, 71] 72).symm
lemma extension_638_73 : a k 73*normalRep k 638=(-normalRep k 746) := by
  change a k 73*walk k 33 [46, 48, 51, 64, 36, 71]=(-walk k 33 [45, 6, 7, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_517 (a k) (relation_zero k) (e k 33)
lemma arrow_span_638 (b : Fin 75) : a k b*normalRep k 638 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_638_72 k]
      exact normal_mem k 748
    · rw [extension_638_73 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 746)
  · rw [show a k b*normalRep k 638=0 from arrow_incompatible k b 33 44 [46, 48, 51, 64, 36, 71] (normal_endpoints 638) h]
    exact Submodule.zero_mem _
lemma extension_639_66 : a k 66*normalRep k 639=normalRep k 749 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8] 66).symm
lemma extension_639_67 : a k 67*normalRep k 639=0 := by
  change a k 67*walk k 34 [47, 7, 17, 21, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_439 (a k) (relation_zero k) (e k 34)
lemma extension_639_68 : a k 68*normalRep k 639=normalRep k 750 := by
  exact (walk_snoc k 34 [47, 7, 17, 21, 69, 8] 68).symm
lemma arrow_span_639 (b : Fin 75) : a k b*normalRep k 639 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_639_66 k]
      exact normal_mem k 749
    · rw [extension_639_67 k]
      exact Submodule.zero_mem _
    · rw [extension_639_68 k]
      exact normal_mem k 750
  · rw [show a k b*normalRep k 639=0 from arrow_incompatible k b 34 42 [47, 7, 17, 21, 69, 8] (normal_endpoints 639) h]
    exact Submodule.zero_mem _
lemma extension_640_3 : a k 3*normalRep k 640=normalRep k 750 := by
  change a k 3*walk k 34 [47, 7, 17, 21, 70, 22]=walk k 34 [47, 7, 17, 21, 69, 8, 68]
  rw [← walk_snoc]
  exact Universal.mul_reduced_458 (a k) (relation_zero k) (e k 34)
lemma arrow_span_640 (b : Fin 75) : a k b*normalRep k 640 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_640_3 k]
      exact normal_mem k 750
  · rw [show a k b*normalRep k 640=0 from arrow_incompatible k b 34 3 [47, 7, 17, 21, 70, 22] (normal_endpoints 640) h]
    exact Submodule.zero_mem _
lemma extension_641_37 : a k 37*normalRep k 641=(-normalRep k 749) := by
  change a k 37*walk k 34 [48, 51, 64, 36, 71, 72]=(-walk k 34 [47, 7, 17, 21, 69, 8, 66])
  rw [← walk_snoc]
  exact Universal.mul_reduced_518 (a k) (relation_zero k) (e k 34)
lemma extension_641_38 : a k 38*normalRep k 641=normalRep k 751 := by
  exact (walk_snoc k 34 [48, 51, 64, 36, 71, 72] 38).symm
lemma arrow_span_641 (b : Fin 75) : a k b*normalRep k 641 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_641_37 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 749)
    · rw [extension_641_38 k]
      exact normal_mem k 751
  · rw [show a k b*normalRep k 641=0 from arrow_incompatible k b 34 29 [48, 51, 64, 36, 71, 72] (normal_endpoints 641) h]
    exact Submodule.zero_mem _
lemma extension_642_9 : a k 9*normalRep k 642=normalRep k 752 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 18] 9).symm
lemma arrow_span_642 (b : Fin 75) : a k b*normalRep k 642 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_642_9 k]
      exact normal_mem k 752
  · rw [show a k b*normalRep k 642=0 from arrow_incompatible k b 35 9 [49, 69, 8, 66, 24, 18] (normal_endpoints 642) h]
    exact Submodule.zero_mem _
lemma extension_643_52 : a k 52*normalRep k 643=normalRep k 752 := by
  change a k 52*walk k 35 [49, 69, 8, 66, 24, 19]=walk k 35 [49, 69, 8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_452 (a k) (relation_zero k) (e k 35)
lemma extension_643_53 : a k 53*normalRep k 643=normalRep k 753 := by
  exact (walk_snoc k 35 [49, 69, 8, 66, 24, 19] 53).symm
lemma arrow_span_643 (b : Fin 75) : a k b*normalRep k 643 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_643_52 k]
      exact normal_mem k 752
    · rw [extension_643_53 k]
      exact normal_mem k 753
  · rw [show a k b*normalRep k 643=0 from arrow_incompatible k b 35 37 [49, 69, 8, 66, 24, 19] (normal_endpoints 643) h]
    exact Submodule.zero_mem _
lemma extension_644_4 : a k 4*normalRep k 644=normalRep k 753 := by
  change a k 4*walk k 35 [49, 69, 8, 66, 25, 60]=walk k 35 [49, 69, 8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_502 (a k) (relation_zero k) (e k 35)
lemma arrow_span_644 (b : Fin 75) : a k b*normalRep k 644 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_644_4 k]
      exact normal_mem k 753
  · rw [show a k b*normalRep k 644=0 from arrow_incompatible k b 35 4 [49, 69, 8, 66, 25, 60] (normal_endpoints 644) h]
    exact Submodule.zero_mem _
lemma extension_645_24 : a k 24*normalRep k 645=normalRep k 754 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66] 24).symm
lemma extension_645_25 : a k 25*normalRep k 645=normalRep k 755 := by
  exact (walk_snoc k 36 [50, 17, 21, 69, 8, 66] 25).symm
lemma arrow_span_645 (b : Fin 75) : a k b*normalRep k 645 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_645_24 k]
      exact normal_mem k 754
    · rw [extension_645_25 k]
      exact normal_mem k 755
  · rw [show a k b*normalRep k 645=0 from arrow_incompatible k b 36 20 [50, 17, 21, 69, 8, 66] (normal_endpoints 645) h]
    exact Submodule.zero_mem _
lemma extension_646_39 : a k 39*normalRep k 646=0 := by
  change a k 39*walk k 36 [50, 17, 21, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_427 (a k) (relation_zero k) (e k 36)
lemma extension_646_40 : a k 40*normalRep k 646=(-normalRep k 755) := by
  change a k 40*walk k 36 [50, 17, 21, 69, 8, 68]=(-walk k 36 [50, 17, 21, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_511 (a k) (relation_zero k) (e k 36)
lemma arrow_span_646 (b : Fin 75) : a k b*normalRep k 646 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_646_39 k]
      exact Submodule.zero_mem _
    · rw [extension_646_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 755)
  · rw [show a k b*normalRep k 646=0 from arrow_incompatible k b 36 30 [50, 17, 21, 69, 8, 68] (normal_endpoints 646) h]
    exact Submodule.zero_mem _
lemma extension_647_28 : a k 28*normalRep k 647=normalRep k 756 := by
  exact (walk_snoc k 36 [51, 64, 36, 71, 72, 38] 28).symm
lemma extension_647_29 : a k 29*normalRep k 647=(-normalRep k 754) := by
  change a k 29*walk k 36 [51, 64, 36, 71, 72, 38]=(-walk k 36 [50, 17, 21, 69, 8, 66, 24])
  rw [← walk_snoc]
  exact Universal.mul_reduced_476 (a k) (relation_zero k) (e k 36)
lemma arrow_span_647 (b : Fin 75) : a k b*normalRep k 647 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_647_28 k]
      exact normal_mem k 756
    · rw [extension_647_29 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 754)
  · rw [show a k b*normalRep k 647=0 from arrow_incompatible k b 36 23 [51, 64, 36, 71, 72, 38] (normal_endpoints 647) h]
    exact Submodule.zero_mem _
lemma extension_648_20 : a k 20*normalRep k 648=0 := by
  change a k 20*walk k 37 [52, 41, 43, 47, 7, 17]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_449 (a k) (relation_zero k) (e k 37)
lemma extension_648_21 : a k 21*normalRep k 648=normalRep k 757 := by
  exact (walk_snoc k 37 [52, 41, 43, 47, 7, 17] 21).symm
lemma arrow_span_648 (b : Fin 75) : a k b*normalRep k 648 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_648_20 k]
      exact Submodule.zero_mem _
    · rw [extension_648_21 k]
      exact normal_mem k 757
  · rw [show a k b*normalRep k 648=0 from arrow_incompatible k b 37 18 [52, 41, 43, 47, 7, 17] (normal_endpoints 648) h]
    exact Submodule.zero_mem _
lemma extension_649_36 : a k 36*normalRep k 649=normalRep k 758 := by
  exact (walk_snoc k 37 [52, 41, 43, 48, 51, 64] 36).symm
lemma arrow_span_649 (b : Fin 75) : a k b*normalRep k 649 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_649_36 k]
      exact normal_mem k 758
  · rw [show a k b*normalRep k 649=0 from arrow_incompatible k b 37 28 [52, 41, 43, 48, 51, 64] (normal_endpoints 649) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
