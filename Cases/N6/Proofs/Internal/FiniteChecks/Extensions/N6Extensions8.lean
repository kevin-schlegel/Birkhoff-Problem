import N6NormalData
import N6Reduced3
import N6Reduced4
import N6Reduced5
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_400_49 : a k 49*normalRep k 400=(-normalRep k 515) + normalRep k 516 := by
  change a k 49*walk k 32 [43, 48, 51, 65]=(-walk k 32 [43, 47, 7, 17, 21]) + walk k 32 [43, 48, 51, 64, 36]
  rw [← walk_snoc]
  exact Universal.mul_reduced_298 (a k) (relation_zero k) (e k 32)
lemma arrow_span_400 (b : Fin 75) : a k b*normalRep k 400 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_400_49 k]
      exact (normalSpan k).add_mem ((normalSpan k).smul_mem (-1:k) (normal_mem k 515)) (normal_mem k 516)
  · rw [show a k b*normalRep k 400=0 from arrow_incompatible k b 32 35 [43, 48, 51, 65] (normal_endpoints 400) h]
    exact Submodule.zero_mem _
lemma extension_401_20 : a k 20*normalRep k 401=normalRep k 517 := by
  exact (walk_snoc k 32 [44, 57, 5, 63] 20).symm
lemma extension_401_21 : a k 21*normalRep k 401=0 := by
  change a k 21*walk k 32 [44, 57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_299 (a k) (relation_zero k) (e k 32)
lemma arrow_span_401 (b : Fin 75) : a k b*normalRep k 401 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_401_20 k]
      exact normal_mem k 517
    · rw [extension_401_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 401=0 from arrow_incompatible k b 32 18 [44, 57, 5, 63] (normal_endpoints 401) h]
    exact Submodule.zero_mem _
lemma extension_402_20 : a k 20*normalRep k 402=0 := by
  change a k 20*walk k 33 [45, 6, 7, 17]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_236 (a k) (relation_zero k) (e k 33)
lemma extension_402_21 : a k 21*normalRep k 402=normalRep k 518 := by
  exact (walk_snoc k 33 [45, 6, 7, 17] 21).symm
lemma arrow_span_402 (b : Fin 75) : a k b*normalRep k 402 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_402_20 k]
      exact Submodule.zero_mem _
    · rw [extension_402_21 k]
      exact normal_mem k 518
  · rw [show a k b*normalRep k 402=0 from arrow_incompatible k b 33 18 [45, 6, 7, 17] (normal_endpoints 402) h]
    exact Submodule.zero_mem _
lemma extension_403_36 : a k 36*normalRep k 403=normalRep k 519 := by
  exact (walk_snoc k 33 [46, 48, 51, 64] 36).symm
lemma arrow_span_403 (b : Fin 75) : a k b*normalRep k 403 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_403_36 k]
      exact normal_mem k 519
  · rw [show a k b*normalRep k 403=0 from arrow_incompatible k b 33 28 [46, 48, 51, 64] (normal_endpoints 403) h]
    exact Submodule.zero_mem _
lemma extension_404_49 : a k 49*normalRep k 404=(-normalRep k 518) + normalRep k 519 := by
  change a k 49*walk k 33 [46, 48, 51, 65]=(-walk k 33 [45, 6, 7, 17, 21]) + walk k 33 [46, 48, 51, 64, 36]
  rw [← walk_snoc]
  exact Universal.mul_reduced_300 (a k) (relation_zero k) (e k 33)
lemma arrow_span_404 (b : Fin 75) : a k b*normalRep k 404 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_404_49 k]
      exact (normalSpan k).add_mem ((normalSpan k).smul_mem (-1:k) (normal_mem k 518)) (normal_mem k 519)
  · rw [show a k b*normalRep k 404=0 from arrow_incompatible k b 33 35 [46, 48, 51, 65] (normal_endpoints 404) h]
    exact Submodule.zero_mem _
lemma extension_405_69 : a k 69*normalRep k 405=normalRep k 520 := by
  exact (walk_snoc k 34 [47, 7, 17, 21] 69).symm
lemma extension_405_70 : a k 70*normalRep k 405=normalRep k 521 := by
  exact (walk_snoc k 34 [47, 7, 17, 21] 70).symm
lemma extension_405_71 : a k 71*normalRep k 405=0 := by
  change a k 71*walk k 34 [47, 7, 17, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_243 (a k) (relation_zero k) (e k 34)
lemma arrow_span_405 (b : Fin 75) : a k b*normalRep k 405 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_405_69 k]
      exact normal_mem k 520
    · rw [extension_405_70 k]
      exact normal_mem k 521
    · rw [extension_405_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 405=0 from arrow_incompatible k b 34 43 [47, 7, 17, 21] (normal_endpoints 405) h]
    exact Submodule.zero_mem _
lemma extension_406_69 : a k 69*normalRep k 406=0 := by
  change a k 69*walk k 34 [48, 51, 64, 36]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_260 (a k) (relation_zero k) (e k 34)
lemma extension_406_70 : a k 70*normalRep k 406=normalRep k 521 := by
  change a k 70*walk k 34 [48, 51, 64, 36]=walk k 34 [47, 7, 17, 21, 70]
  rw [← walk_snoc]
  exact Universal.mul_reduced_274 (a k) (relation_zero k) (e k 34)
lemma extension_406_71 : a k 71*normalRep k 406=normalRep k 522 := by
  exact (walk_snoc k 34 [48, 51, 64, 36] 71).symm
lemma arrow_span_406 (b : Fin 75) : a k b*normalRep k 406 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_406_69 k]
      exact Submodule.zero_mem _
    · rw [extension_406_70 k]
      exact normal_mem k 521
    · rw [extension_406_71 k]
      exact normal_mem k 522
  · rw [show a k b*normalRep k 406=0 from arrow_incompatible k b 34 43 [48, 51, 64, 36] (normal_endpoints 406) h]
    exact Submodule.zero_mem _
lemma extension_407_24 : a k 24*normalRep k 407=normalRep k 523 := by
  exact (walk_snoc k 35 [49, 69, 8, 66] 24).symm
lemma extension_407_25 : a k 25*normalRep k 407=normalRep k 524 := by
  exact (walk_snoc k 35 [49, 69, 8, 66] 25).symm
lemma arrow_span_407 (b : Fin 75) : a k b*normalRep k 407 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_407_24 k]
      exact normal_mem k 523
    · rw [extension_407_25 k]
      exact normal_mem k 524
  · rw [show a k b*normalRep k 407=0 from arrow_incompatible k b 35 20 [49, 69, 8, 66] (normal_endpoints 407) h]
    exact Submodule.zero_mem _
lemma extension_408_39 : a k 39*normalRep k 408=0 := by
  change a k 39*walk k 35 [49, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_223 (a k) (relation_zero k) (e k 35)
lemma extension_408_40 : a k 40*normalRep k 408=(-normalRep k 524) := by
  change a k 40*walk k 35 [49, 69, 8, 68]=(-walk k 35 [49, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_304 (a k) (relation_zero k) (e k 35)
lemma arrow_span_408 (b : Fin 75) : a k b*normalRep k 408 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_408_39 k]
      exact Submodule.zero_mem _
    · rw [extension_408_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 524)
  · rw [show a k b*normalRep k 408=0 from arrow_incompatible k b 35 30 [49, 69, 8, 68] (normal_endpoints 408) h]
    exact Submodule.zero_mem _
lemma extension_409_28 : a k 28*normalRep k 409=normalRep k 525 := by
  exact (walk_snoc k 35 [49, 71, 72, 38] 28).symm
lemma extension_409_29 : a k 29*normalRep k 409=normalRep k 523 := by
  change a k 29*walk k 35 [49, 71, 72, 38]=walk k 35 [49, 69, 8, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_263 (a k) (relation_zero k) (e k 35)
lemma arrow_span_409 (b : Fin 75) : a k b*normalRep k 409 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_409_28 k]
      exact normal_mem k 525
    · rw [extension_409_29 k]
      exact normal_mem k 523
  · rw [show a k b*normalRep k 409=0 from arrow_incompatible k b 35 23 [49, 71, 72, 38] (normal_endpoints 409) h]
    exact Submodule.zero_mem _
lemma extension_410_8 : a k 8*normalRep k 410=normalRep k 526 := by
  exact (walk_snoc k 36 [50, 17, 21, 69] 8).symm
lemma arrow_span_410 (b : Fin 75) : a k b*normalRep k 410 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_410_8 k]
      exact normal_mem k 526
  · rw [show a k b*normalRep k 410=0 from arrow_incompatible k b 36 8 [50, 17, 21, 69] (normal_endpoints 410) h]
    exact Submodule.zero_mem _
lemma extension_411_22 : a k 22*normalRep k 411=normalRep k 527 := by
  exact (walk_snoc k 36 [50, 17, 21, 70] 22).symm
lemma extension_411_23 : a k 23*normalRep k 411=(-normalRep k 526) := by
  change a k 23*walk k 36 [50, 17, 21, 70]=(-walk k 36 [50, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_308 (a k) (relation_zero k) (e k 36)
lemma arrow_span_411 (b : Fin 75) : a k b*normalRep k 411 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_411_22 k]
      exact normal_mem k 527
    · rw [extension_411_23 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 526)
  · rw [show a k b*normalRep k 411=0 from arrow_incompatible k b 36 19 [50, 17, 21, 70] (normal_endpoints 411) h]
    exact Submodule.zero_mem _
lemma extension_412_72 : a k 72*normalRep k 412=normalRep k 528 := by
  exact (walk_snoc k 36 [51, 64, 36, 71] 72).symm
lemma extension_412_73 : a k 73*normalRep k 412=(-normalRep k 526) := by
  change a k 73*walk k 36 [51, 64, 36, 71]=(-walk k 36 [50, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_309 (a k) (relation_zero k) (e k 36)
lemma arrow_span_412 (b : Fin 75) : a k b*normalRep k 412 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_412_72 k]
      exact normal_mem k 528
    · rw [extension_412_73 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 526)
  · rw [show a k b*normalRep k 412=0 from arrow_incompatible k b 36 44 [51, 64, 36, 71] (normal_endpoints 412) h]
    exact Submodule.zero_mem _
lemma extension_413_7 : a k 7*normalRep k 413=normalRep k 529 := by
  exact (walk_snoc k 37 [52, 41, 43, 47] 7).symm
lemma arrow_span_413 (b : Fin 75) : a k b*normalRep k 413 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_413_7 k]
      exact normal_mem k 529
  · rw [show a k b*normalRep k 413=0 from arrow_incompatible k b 37 7 [52, 41, 43, 47] (normal_endpoints 413) h]
    exact Submodule.zero_mem _
lemma extension_414_50 : a k 50*normalRep k 414=normalRep k 529 := by
  change a k 50*walk k 37 [52, 41, 43, 48]=walk k 37 [52, 41, 43, 47, 7]
  rw [← walk_snoc]
  exact Universal.mul_reduced_273 (a k) (relation_zero k) (e k 37)
lemma extension_414_51 : a k 51*normalRep k 414=normalRep k 530 := by
  exact (walk_snoc k 37 [52, 41, 43, 48] 51).symm
lemma arrow_span_414 (b : Fin 75) : a k b*normalRep k 414 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_414_50 k]
      exact normal_mem k 529
    · rw [extension_414_51 k]
      exact normal_mem k 530
  · rw [show a k b*normalRep k 414=0 from arrow_incompatible k b 37 36 [52, 41, 43, 48] (normal_endpoints 414) h]
    exact Submodule.zero_mem _
lemma extension_415_5 : a k 5*normalRep k 415=normalRep k 531 := by
  exact (walk_snoc k 37 [52, 41, 44, 57] 5).symm
lemma arrow_span_415 (b : Fin 75) : a k b*normalRep k 415 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_415_5 k]
      exact normal_mem k 531
  · rw [show a k b*normalRep k 415=0 from arrow_incompatible k b 37 5 [52, 41, 44, 57] (normal_endpoints 415) h]
    exact Submodule.zero_mem _
lemma extension_416_33 : a k 33*normalRep k 416=normalRep k 532 := by
  exact (walk_snoc k 37 [52, 41, 44, 58] 33).symm
lemma extension_416_34 : a k 34*normalRep k 416=normalRep k 531 + normalRep k 530 := by
  change a k 34*walk k 37 [52, 41, 44, 58]=walk k 37 [52, 41, 44, 57, 5] + walk k 37 [52, 41, 43, 48, 51]
  rw [← walk_snoc]
  exact Universal.mul_reduced_290 (a k) (relation_zero k) (e k 37)
lemma arrow_span_416 (b : Fin 75) : a k b*normalRep k 416 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_416_33 k]
      exact normal_mem k 532
    · rw [extension_416_34 k]
      exact (normalSpan k).add_mem (normal_mem k 531) (normal_mem k 530)
  · rw [show a k b*normalRep k 416=0 from arrow_incompatible k b 37 26 [52, 41, 44, 58] (normal_endpoints 416) h]
    exact Submodule.zero_mem _
lemma extension_417_33 : a k 33*normalRep k 417=0 := by
  change a k 33*walk k 37 [53, 54, 15, 1]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_210 (a k) (relation_zero k) (e k 37)
lemma extension_417_34 : a k 34*normalRep k 417=normalRep k 531 := by
  change a k 34*walk k 37 [53, 54, 15, 1]=walk k 37 [52, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_291 (a k) (relation_zero k) (e k 37)
lemma arrow_span_417 (b : Fin 75) : a k b*normalRep k 417 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_417_33 k]
      exact Submodule.zero_mem _
    · rw [extension_417_34 k]
      exact normal_mem k 531
  · rw [show a k b*normalRep k 417=0 from arrow_incompatible k b 37 26 [53, 54, 15, 1] (normal_endpoints 417) h]
    exact Submodule.zero_mem _
lemma extension_418_63 : a k 63*normalRep k 418=normalRep k 533 := by
  exact (walk_snoc k 38 [54, 15, 1, 34] 63).symm
lemma extension_418_64 : a k 64*normalRep k 418=0 := by
  change a k 64*walk k 38 [54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_211 (a k) (relation_zero k) (e k 38)
lemma extension_418_65 : a k 65*normalRep k 418=0 := by
  change a k 65*walk k 38 [54, 15, 1, 34]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_222 (a k) (relation_zero k) (e k 38)
lemma arrow_span_418 (b : Fin 75) : a k b*normalRep k 418 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_418_63 k]
      exact normal_mem k 533
    · rw [extension_418_64 k]
      exact Submodule.zero_mem _
    · rw [extension_418_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 418=0 from arrow_incompatible k b 38 41 [54, 15, 1, 34] (normal_endpoints 418) h]
    exact Submodule.zero_mem _
lemma extension_419_13 : a k 13*normalRep k 419=normalRep k 534 := by
  exact (walk_snoc k 38 [55, 27, 58, 33] 13).symm
lemma arrow_span_419 (b : Fin 75) : a k b*normalRep k 419 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_419_13 k]
      exact normal_mem k 534
  · rw [show a k b*normalRep k 419=0 from arrow_incompatible k b 38 13 [55, 27, 58, 33] (normal_endpoints 419) h]
    exact Submodule.zero_mem _
lemma extension_420_63 : a k 63*normalRep k 420=normalRep k 535 := by
  exact (walk_snoc k 38 [55, 27, 58, 34] 63).symm
lemma extension_420_64 : a k 64*normalRep k 420=normalRep k 536 := by
  exact (walk_snoc k 38 [55, 27, 58, 34] 64).symm
lemma extension_420_65 : a k 65*normalRep k 420=normalRep k 534 := by
  change a k 65*walk k 38 [55, 27, 58, 34]=walk k 38 [55, 27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_258 (a k) (relation_zero k) (e k 38)
lemma arrow_span_420 (b : Fin 75) : a k b*normalRep k 420 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_420_63 k]
      exact normal_mem k 535
    · rw [extension_420_64 k]
      exact normal_mem k 536
    · rw [extension_420_65 k]
      exact normal_mem k 534
  · rw [show a k b*normalRep k 420=0 from arrow_incompatible k b 38 41 [55, 27, 58, 34] (normal_endpoints 420) h]
    exact Submodule.zero_mem _
lemma extension_421_17 : a k 17*normalRep k 421=normalRep k 535 := by
  change a k 17*walk k 38 [55, 27, 59, 50]=walk k 38 [55, 27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_277 (a k) (relation_zero k) (e k 38)
lemma arrow_span_421 (b : Fin 75) : a k b*normalRep k 421 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_421_17 k]
      exact normal_mem k 535
  · rw [show a k b*normalRep k 421=0 from arrow_incompatible k b 38 16 [55, 27, 59, 50] (normal_endpoints 421) h]
    exact Submodule.zero_mem _
lemma extension_422_30 : a k 30*normalRep k 422=normalRep k 537 := by
  exact (walk_snoc k 39 [57, 5, 63, 20] 30).symm
lemma extension_422_31 : a k 31*normalRep k 422=0 := by
  change a k 31*walk k 39 [57, 5, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_241 (a k) (relation_zero k) (e k 39)
lemma arrow_span_422 (b : Fin 75) : a k b*normalRep k 422 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_422_30 k]
      exact normal_mem k 537
    · rw [extension_422_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 422=0 from arrow_incompatible k b 39 24 [57, 5, 63, 20] (normal_endpoints 422) h]
    exact Submodule.zero_mem _
lemma extension_423_69 : a k 69*normalRep k 423=normalRep k 538 := by
  exact (walk_snoc k 39 [58, 33, 13, 49] 69).symm
lemma extension_423_70 : a k 70*normalRep k 423=0 := by
  change a k 70*walk k 39 [58, 33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_275 (a k) (relation_zero k) (e k 39)
lemma extension_423_71 : a k 71*normalRep k 423=normalRep k 539 := by
  exact (walk_snoc k 39 [58, 33, 13, 49] 71).symm
lemma arrow_span_423 (b : Fin 75) : a k b*normalRep k 423 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_423_69 k]
      exact normal_mem k 538
    · rw [extension_423_70 k]
      exact Submodule.zero_mem _
    · rw [extension_423_71 k]
      exact normal_mem k 539
  · rw [show a k b*normalRep k 423=0 from arrow_incompatible k b 39 43 [58, 33, 13, 49] (normal_endpoints 423) h]
    exact Submodule.zero_mem _
lemma extension_424_69 : a k 69*normalRep k 424=(-normalRep k 538) := by
  change a k 69*walk k 39 [58, 34, 63, 21]=(-walk k 39 [58, 33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_261 (a k) (relation_zero k) (e k 39)
lemma extension_424_70 : a k 70*normalRep k 424=normalRep k 540 := by
  exact (walk_snoc k 39 [58, 34, 63, 21] 70).symm
lemma extension_424_71 : a k 71*normalRep k 424=0 := by
  change a k 71*walk k 39 [58, 34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_244 (a k) (relation_zero k) (e k 39)
lemma arrow_span_424 (b : Fin 75) : a k b*normalRep k 424 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_424_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 538)
    · rw [extension_424_70 k]
      exact normal_mem k 540
    · rw [extension_424_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 424=0 from arrow_incompatible k b 39 43 [58, 34, 63, 21] (normal_endpoints 424) h]
    exact Submodule.zero_mem _
lemma extension_425_1 : a k 1*normalRep k 425=normalRep k 541 := by
  exact (walk_snoc k 40 [60, 4, 54, 15] 1).symm
lemma arrow_span_425 (b : Fin 75) : a k b*normalRep k 425 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_425_1 k]
      exact normal_mem k 541
  · rw [show a k b*normalRep k 425=0 from arrow_incompatible k b 40 1 [60, 4, 54, 15] (normal_endpoints 425) h]
    exact Submodule.zero_mem _
lemma extension_426_57 : a k 57*normalRep k 426=normalRep k 542 := by
  exact (walk_snoc k 40 [60, 4, 54, 16] 57).symm
lemma extension_426_58 : a k 58*normalRep k 426=normalRep k 541 := by
  change a k 58*walk k 40 [60, 4, 54, 16]=walk k 40 [60, 4, 54, 15, 1]
  rw [← walk_snoc]
  exact Universal.mul_reduced_231 (a k) (relation_zero k) (e k 40)
lemma extension_426_59 : a k 59*normalRep k 426=0 := by
  change a k 59*walk k 40 [60, 4, 54, 16]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_233 (a k) (relation_zero k) (e k 40)
lemma arrow_span_426 (b : Fin 75) : a k b*normalRep k 426 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_426_57 k]
      exact normal_mem k 542
    · rw [extension_426_58 k]
      exact normal_mem k 541
    · rw [extension_426_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 426=0 from arrow_incompatible k b 40 39 [60, 4, 54, 16] (normal_endpoints 426) h]
    exact Submodule.zero_mem _
lemma extension_427_57 : a k 57*normalRep k 427=0 := by
  change a k 57*walk k 40 [61, 35, 55, 27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_253 (a k) (relation_zero k) (e k 40)
lemma extension_427_58 : a k 58*normalRep k 427=normalRep k 543 := by
  exact (walk_snoc k 40 [61, 35, 55, 27] 58).symm
lemma extension_427_59 : a k 59*normalRep k 427=normalRep k 544 := by
  exact (walk_snoc k 40 [61, 35, 55, 27] 59).symm
lemma arrow_span_427 (b : Fin 75) : a k b*normalRep k 427 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_427_57 k]
      exact Submodule.zero_mem _
    · rw [extension_427_58 k]
      exact normal_mem k 543
    · rw [extension_427_59 k]
      exact normal_mem k 544
  · rw [show a k b*normalRep k 427=0 from arrow_incompatible k b 40 39 [61, 35, 55, 27] (normal_endpoints 427) h]
    exact Submodule.zero_mem _
lemma extension_428_47 : a k 47*normalRep k 428=normalRep k 545 := by
  exact (walk_snoc k 40 [61, 35, 56, 43] 47).symm
lemma extension_428_48 : a k 48*normalRep k 428=normalRep k 544 := by
  change a k 48*walk k 40 [61, 35, 56, 43]=walk k 40 [61, 35, 55, 27, 59]
  rw [← walk_snoc]
  exact Universal.mul_reduced_270 (a k) (relation_zero k) (e k 40)
lemma arrow_span_428 (b : Fin 75) : a k b*normalRep k 428 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_428_47 k]
      exact normal_mem k 545
    · rw [extension_428_48 k]
      exact normal_mem k 544
  · rw [show a k b*normalRep k 428=0 from arrow_incompatible k b 40 34 [61, 35, 56, 43] (normal_endpoints 428) h]
    exact Submodule.zero_mem _
lemma extension_429_6 : a k 6*normalRep k 429=normalRep k 545 := by
  change a k 6*walk k 40 [62, 52, 42, 45]=walk k 40 [61, 35, 56, 43, 47]
  rw [← walk_snoc]
  exact Universal.mul_reduced_271 (a k) (relation_zero k) (e k 40)
lemma arrow_span_429 (b : Fin 75) : a k b*normalRep k 429 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_429_6 k]
      exact normal_mem k 545
  · rw [show a k b*normalRep k 429=0 from arrow_incompatible k b 40 6 [62, 52, 42, 45] (normal_endpoints 429) h]
    exact Submodule.zero_mem _
lemma extension_430_0 : a k 0*normalRep k 430=normalRep k 546 := by
  exact (walk_snoc k 41 [63, 20, 30, 2] 0).symm
lemma arrow_span_430 (b : Fin 75) : a k b*normalRep k 430 ∈ normalSpan k := by
  by_cases h : arrowSource b=0
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [0] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_430_0 k]
      exact normal_mem k 546
  · rw [show a k b*normalRep k 430=0 from arrow_incompatible k b 41 0 [63, 20, 30, 2] (normal_endpoints 430) h]
    exact Submodule.zero_mem _
lemma extension_431_66 : a k 66*normalRep k 431=normalRep k 547 := by
  exact (walk_snoc k 41 [63, 21, 69, 8] 66).symm
lemma extension_431_67 : a k 67*normalRep k 431=0 := by
  change a k 67*walk k 41 [63, 21, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_226 (a k) (relation_zero k) (e k 41)
lemma extension_431_68 : a k 68*normalRep k 431=normalRep k 548 := by
  exact (walk_snoc k 41 [63, 21, 69, 8] 68).symm
lemma arrow_span_431 (b : Fin 75) : a k b*normalRep k 431 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_431_66 k]
      exact normal_mem k 547
    · rw [extension_431_67 k]
      exact Submodule.zero_mem _
    · rw [extension_431_68 k]
      exact normal_mem k 548
  · rw [show a k b*normalRep k 431=0 from arrow_incompatible k b 41 42 [63, 21, 69, 8] (normal_endpoints 431) h]
    exact Submodule.zero_mem _
lemma extension_432_3 : a k 3*normalRep k 432=normalRep k 548 := by
  change a k 3*walk k 41 [63, 21, 70, 22]=walk k 41 [63, 21, 69, 8, 68]
  rw [← walk_snoc]
  exact Universal.mul_reduced_246 (a k) (relation_zero k) (e k 41)
lemma arrow_span_432 (b : Fin 75) : a k b*normalRep k 432 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_432_3 k]
      exact normal_mem k 548
  · rw [show a k b*normalRep k 432=0 from arrow_incompatible k b 41 3 [63, 21, 70, 22] (normal_endpoints 432) h]
    exact Submodule.zero_mem _
lemma extension_433_37 : a k 37*normalRep k 433=(-normalRep k 547) := by
  change a k 37*walk k 41 [64, 36, 71, 72]=(-walk k 41 [63, 21, 69, 8, 66])
  rw [← walk_snoc]
  exact Universal.mul_reduced_312 (a k) (relation_zero k) (e k 41)
lemma extension_433_38 : a k 38*normalRep k 433=normalRep k 549 := by
  exact (walk_snoc k 41 [64, 36, 71, 72] 38).symm
lemma arrow_span_433 (b : Fin 75) : a k b*normalRep k 433 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_433_37 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 547)
    · rw [extension_433_38 k]
      exact normal_mem k 549
  · rw [show a k b*normalRep k 433=0 from arrow_incompatible k b 41 29 [64, 36, 71, 72] (normal_endpoints 433) h]
    exact Submodule.zero_mem _
lemma extension_434_41 : a k 41*normalRep k 434=normalRep k 550 := by
  exact (walk_snoc k 42 [66, 24, 18, 9] 41).symm
lemma extension_434_42 : a k 42*normalRep k 434=0 := by
  change a k 42*walk k 42 [66, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_229 (a k) (relation_zero k) (e k 42)
lemma arrow_span_434 (b : Fin 75) : a k b*normalRep k 434 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_434_41 k]
      exact normal_mem k 550
    · rw [extension_434_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 434=0 from arrow_incompatible k b 42 31 [66, 24, 18, 9] (normal_endpoints 434) h]
    exact Submodule.zero_mem _
lemma extension_435_54 : a k 54*normalRep k 435=normalRep k 551 := by
  exact (walk_snoc k 42 [66, 24, 19, 53] 54).symm
lemma extension_435_55 : a k 55*normalRep k 435=0 := by
  change a k 55*walk k 42 [66, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_217 (a k) (relation_zero k) (e k 42)
lemma extension_435_56 : a k 56*normalRep k 435=normalRep k 550 := by
  change a k 56*walk k 42 [66, 24, 19, 53]=walk k 42 [66, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_280 (a k) (relation_zero k) (e k 42)
lemma arrow_span_435 (b : Fin 75) : a k b*normalRep k 435 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_435_54 k]
      exact normal_mem k 551
    · rw [extension_435_55 k]
      exact Submodule.zero_mem _
    · rw [extension_435_56 k]
      exact normal_mem k 550
  · rw [show a k b*normalRep k 435=0 from arrow_incompatible k b 42 38 [66, 24, 19, 53] (normal_endpoints 435) h]
    exact Submodule.zero_mem _
lemma extension_436_54 : a k 54*normalRep k 436=0 := by
  change a k 54*walk k 42 [67, 32, 61, 35]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_259 (a k) (relation_zero k) (e k 42)
lemma extension_436_55 : a k 55*normalRep k 436=normalRep k 552 := by
  exact (walk_snoc k 42 [67, 32, 61, 35] 55).symm
lemma extension_436_56 : a k 56*normalRep k 436=normalRep k 553 := by
  exact (walk_snoc k 42 [67, 32, 61, 35] 56).symm
lemma arrow_span_436 (b : Fin 75) : a k b*normalRep k 436 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_436_54 k]
      exact Submodule.zero_mem _
    · rw [extension_436_55 k]
      exact normal_mem k 552
    · rw [extension_436_56 k]
      exact normal_mem k 553
  · rw [show a k b*normalRep k 436=0 from arrow_incompatible k b 42 38 [67, 32, 61, 35] (normal_endpoints 436) h]
    exact Submodule.zero_mem _
lemma extension_437_41 : a k 41*normalRep k 437=normalRep k 553 := by
  change a k 41*walk k 42 [67, 32, 62, 52]=walk k 42 [67, 32, 61, 35, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_281 (a k) (relation_zero k) (e k 42)
lemma extension_437_42 : a k 42*normalRep k 437=normalRep k 554 := by
  exact (walk_snoc k 42 [67, 32, 62, 52] 42).symm
lemma arrow_span_437 (b : Fin 75) : a k b*normalRep k 437 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_437_41 k]
      exact normal_mem k 553
    · rw [extension_437_42 k]
      exact normal_mem k 554
  · rw [show a k b*normalRep k 437=0 from arrow_incompatible k b 42 31 [67, 32, 62, 52] (normal_endpoints 437) h]
    exact Submodule.zero_mem _
lemma extension_438_18 : a k 18*normalRep k 438=normalRep k 555 := by
  exact (walk_snoc k 43 [69, 8, 66, 24] 18).symm
lemma extension_438_19 : a k 19*normalRep k 438=normalRep k 556 := by
  exact (walk_snoc k 43 [69, 8, 66, 24] 19).symm
lemma arrow_span_438 (b : Fin 75) : a k b*normalRep k 438 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_438_18 k]
      exact normal_mem k 555
    · rw [extension_438_19 k]
      exact normal_mem k 556
  · rw [show a k b*normalRep k 438=0 from arrow_incompatible k b 43 17 [69, 8, 66, 24] (normal_endpoints 438) h]
    exact Submodule.zero_mem _
lemma extension_439_60 : a k 60*normalRep k 439=normalRep k 557 := by
  exact (walk_snoc k 43 [69, 8, 66, 25] 60).symm
lemma extension_439_61 : a k 61*normalRep k 439=0 := by
  change a k 61*walk k 43 [69, 8, 66, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_247 (a k) (relation_zero k) (e k 43)
lemma extension_439_62 : a k 62*normalRep k 439=normalRep k 556 := by
  change a k 62*walk k 43 [69, 8, 66, 25]=walk k 43 [69, 8, 66, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_249 (a k) (relation_zero k) (e k 43)
lemma arrow_span_439 (b : Fin 75) : a k b*normalRep k 439 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_439_60 k]
      exact normal_mem k 557
    · rw [extension_439_61 k]
      exact Submodule.zero_mem _
    · rw [extension_439_62 k]
      exact normal_mem k 556
  · rw [show a k b*normalRep k 439=0 from arrow_incompatible k b 43 40 [69, 8, 66, 25] (normal_endpoints 439) h]
    exact Submodule.zero_mem _
lemma extension_440_60 : a k 60*normalRep k 440=normalRep k 558 := by
  exact (walk_snoc k 43 [70, 22, 3, 40] 60).symm
lemma extension_440_61 : a k 61*normalRep k 440=0 := by
  change a k 61*walk k 43 [70, 22, 3, 40]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_248 (a k) (relation_zero k) (e k 43)
lemma extension_440_62 : a k 62*normalRep k 440=normalRep k 559 := by
  exact (walk_snoc k 43 [70, 22, 3, 40] 62).symm
lemma arrow_span_440 (b : Fin 75) : a k b*normalRep k 440 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_440_60 k]
      exact normal_mem k 558
    · rw [extension_440_61 k]
      exact Submodule.zero_mem _
    · rw [extension_440_62 k]
      exact normal_mem k 559
  · rw [show a k b*normalRep k 440=0 from arrow_incompatible k b 43 40 [70, 22, 3, 40] (normal_endpoints 440) h]
    exact Submodule.zero_mem _
lemma extension_441_18 : a k 18*normalRep k 441=normalRep k 560 := by
  exact (walk_snoc k 43 [70, 23, 66, 24] 18).symm
lemma extension_441_19 : a k 19*normalRep k 441=normalRep k 559 := by
  change a k 19*walk k 43 [70, 23, 66, 24]=walk k 43 [70, 22, 3, 40, 62]
  rw [← walk_snoc]
  exact Universal.mul_reduced_250 (a k) (relation_zero k) (e k 43)
lemma arrow_span_441 (b : Fin 75) : a k b*normalRep k 441 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_441_18 k]
      exact normal_mem k 560
    · rw [extension_441_19 k]
      exact normal_mem k 559
  · rw [show a k b*normalRep k 441=0 from arrow_incompatible k b 43 17 [70, 23, 66, 24] (normal_endpoints 441) h]
    exact Submodule.zero_mem _
lemma extension_442_14 : a k 14*normalRep k 442=normalRep k 555 + normalRep k 560 := by
  change a k 14*walk k 43 [71, 72, 38, 28]=walk k 43 [69, 8, 66, 24, 18] + walk k 43 [70, 23, 66, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_254 (a k) (relation_zero k) (e k 43)
lemma arrow_span_442 (b : Fin 75) : a k b*normalRep k 442 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_442_14 k]
      exact (normalSpan k).add_mem (normal_mem k 555) (normal_mem k 560)
  · rw [show a k b*normalRep k 442=0 from arrow_incompatible k b 43 14 [71, 72, 38, 28] (normal_endpoints 442) h]
    exact Submodule.zero_mem _
lemma extension_443_9 : a k 9*normalRep k 443=normalRep k 561 := by
  exact (walk_snoc k 44 [72, 37, 24, 18] 9).symm
lemma arrow_span_443 (b : Fin 75) : a k b*normalRep k 443 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_443_9 k]
      exact normal_mem k 561
  · rw [show a k b*normalRep k 443=0 from arrow_incompatible k b 44 9 [72, 37, 24, 18] (normal_endpoints 443) h]
    exact Submodule.zero_mem _
lemma extension_444_52 : a k 52*normalRep k 444=normalRep k 561 := by
  change a k 52*walk k 44 [72, 37, 24, 19]=walk k 44 [72, 37, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_239 (a k) (relation_zero k) (e k 44)
lemma extension_444_53 : a k 53*normalRep k 444=normalRep k 562 := by
  exact (walk_snoc k 44 [72, 37, 24, 19] 53).symm
lemma arrow_span_444 (b : Fin 75) : a k b*normalRep k 444 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_444_52 k]
      exact normal_mem k 561
    · rw [extension_444_53 k]
      exact normal_mem k 562
  · rw [show a k b*normalRep k 444=0 from arrow_incompatible k b 44 37 [72, 37, 24, 19] (normal_endpoints 444) h]
    exact Submodule.zero_mem _
lemma extension_445_4 : a k 4*normalRep k 445=normalRep k 562 := by
  change a k 4*walk k 44 [72, 37, 25, 60]=walk k 44 [72, 37, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_294 (a k) (relation_zero k) (e k 44)
lemma arrow_span_445 (b : Fin 75) : a k b*normalRep k 445 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_445_4 k]
      exact normal_mem k 562
  · rw [show a k b*normalRep k 445=0 from arrow_incompatible k b 44 4 [72, 37, 25, 60] (normal_endpoints 445) h]
    exact Submodule.zero_mem _
lemma extension_446_35 : a k 35*normalRep k 446=normalRep k 563 := by
  exact (walk_snoc k 44 [73, 67, 32, 61] 35).symm
lemma arrow_span_446 (b : Fin 75) : a k b*normalRep k 446 ∈ normalSpan k := by
  by_cases h : arrowSource b=27
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [35] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_446_35 k]
      exact normal_mem k 563
  · rw [show a k b*normalRep k 446=0 from arrow_incompatible k b 44 27 [73, 67, 32, 61] (normal_endpoints 446) h]
    exact Submodule.zero_mem _
lemma extension_447_52 : a k 52*normalRep k 447=normalRep k 564 := by
  exact (walk_snoc k 44 [73, 67, 32, 62] 52).symm
lemma extension_447_53 : a k 53*normalRep k 447=normalRep k 563 := by
  change a k 53*walk k 44 [73, 67, 32, 62]=walk k 44 [73, 67, 32, 61, 35]
  rw [← walk_snoc]
  exact Universal.mul_reduced_295 (a k) (relation_zero k) (e k 44)
lemma arrow_span_447 (b : Fin 75) : a k b*normalRep k 447 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_447_52 k]
      exact normal_mem k 564
    · rw [extension_447_53 k]
      exact normal_mem k 563
  · rw [show a k b*normalRep k 447=0 from arrow_incompatible k b 44 37 [73, 67, 32, 62] (normal_endpoints 447) h]
    exact Submodule.zero_mem _
lemma extension_448_30 : a k 30*normalRep k 448=0 := by
  change a k 30*walk k 45 [74, 10, 11, 26]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_251 (a k) (relation_zero k) (e k 45)
lemma extension_448_31 : a k 31*normalRep k 448=normalRep k 565 := by
  exact (walk_snoc k 45 [74, 10, 11, 26] 31).symm
lemma arrow_span_448 (b : Fin 75) : a k b*normalRep k 448 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_448_30 k]
      exact Submodule.zero_mem _
    · rw [extension_448_31 k]
      exact normal_mem k 565
  · rw [show a k b*normalRep k 448=0 from arrow_incompatible k b 45 24 [74, 10, 11, 26] (normal_endpoints 448) h]
    exact Submodule.zero_mem _
lemma extension_449_2 : a k 2*normalRep k 449=normalRep k 566 := by
  exact (walk_snoc k 1 [1, 34, 63, 20, 30] 2).symm
lemma arrow_span_449 (b : Fin 75) : a k b*normalRep k 449 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_449_2 k]
      exact normal_mem k 566
  · rw [show a k b*normalRep k 449=0 from arrow_incompatible k b 1 2 [1, 34, 63, 20, 30] (normal_endpoints 449) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
