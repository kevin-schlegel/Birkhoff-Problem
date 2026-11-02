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
lemma extension_350_37 : a k 37*normalRep k 350=normalRep k 467 := by
  change a k 37*walk k 13 [13, 49, 71, 72]=walk k 13 [13, 49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_311 (a k) (relation_zero k) (e k 13)
lemma extension_350_38 : a k 38*normalRep k 350=normalRep k 469 := by
  exact (walk_snoc k 13 [13, 49, 71, 72] 38).symm
lemma arrow_span_350 (b : Fin 75) : a k b*normalRep k 350 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_350_37 k]
      exact normal_mem k 467
    · rw [extension_350_38 k]
      exact normal_mem k 469
  · rw [show a k b*normalRep k 350=0 from arrow_incompatible k b 13 29 [13, 49, 71, 72] (normal_endpoints 350) h]
    exact Submodule.zero_mem _
lemma extension_351_57 : a k 57*normalRep k 351=normalRep k 470 := by
  exact (walk_snoc k 14 [14, 9, 41, 44] 57).symm
lemma extension_351_58 : a k 58*normalRep k 351=normalRep k 471 := by
  exact (walk_snoc k 14 [14, 9, 41, 44] 58).symm
lemma extension_351_59 : a k 59*normalRep k 351=0 := by
  change a k 59*walk k 14 [14, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_269 (a k) (relation_zero k) (e k 14)
lemma arrow_span_351 (b : Fin 75) : a k b*normalRep k 351 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_351_57 k]
      exact normal_mem k 470
    · rw [extension_351_58 k]
      exact normal_mem k 471
    · rw [extension_351_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 351=0 from arrow_incompatible k b 14 39 [14, 9, 41, 44] (normal_endpoints 351) h]
    exact Submodule.zero_mem _
lemma extension_352_20 : a k 20*normalRep k 352=normalRep k 472 := by
  exact (walk_snoc k 15 [15, 1, 34, 63] 20).symm
lemma extension_352_21 : a k 21*normalRep k 352=0 := by
  change a k 21*walk k 15 [15, 1, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_296 (a k) (relation_zero k) (e k 15)
lemma arrow_span_352 (b : Fin 75) : a k b*normalRep k 352 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_352_20 k]
      exact normal_mem k 472
    · rw [extension_352_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 352=0 from arrow_incompatible k b 15 18 [15, 1, 34, 63] (normal_endpoints 352) h]
    exact Submodule.zero_mem _
lemma extension_353_66 : a k 66*normalRep k 353=normalRep k 473 := by
  exact (walk_snoc k 16 [17, 21, 69, 8] 66).symm
lemma extension_353_67 : a k 67*normalRep k 353=0 := by
  change a k 67*walk k 16 [17, 21, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_225 (a k) (relation_zero k) (e k 16)
lemma extension_353_68 : a k 68*normalRep k 353=normalRep k 474 := by
  exact (walk_snoc k 16 [17, 21, 69, 8] 68).symm
lemma arrow_span_353 (b : Fin 75) : a k b*normalRep k 353 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_353_66 k]
      exact normal_mem k 473
    · rw [extension_353_67 k]
      exact Submodule.zero_mem _
    · rw [extension_353_68 k]
      exact normal_mem k 474
  · rw [show a k b*normalRep k 353=0 from arrow_incompatible k b 16 42 [17, 21, 69, 8] (normal_endpoints 353) h]
    exact Submodule.zero_mem _
lemma extension_354_3 : a k 3*normalRep k 354=normalRep k 474 := by
  change a k 3*walk k 16 [17, 21, 70, 22]=walk k 16 [17, 21, 69, 8, 68]
  rw [← walk_snoc]
  exact Universal.mul_reduced_245 (a k) (relation_zero k) (e k 16)
lemma arrow_span_354 (b : Fin 75) : a k b*normalRep k 354 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_354_3 k]
      exact normal_mem k 474
  · rw [show a k b*normalRep k 354=0 from arrow_incompatible k b 16 3 [17, 21, 70, 22] (normal_endpoints 354) h]
    exact Submodule.zero_mem _
lemma extension_355_57 : a k 57*normalRep k 355=normalRep k 475 := by
  exact (walk_snoc k 17 [18, 9, 41, 44] 57).symm
lemma extension_355_58 : a k 58*normalRep k 355=normalRep k 476 := by
  exact (walk_snoc k 17 [18, 9, 41, 44] 58).symm
lemma extension_355_59 : a k 59*normalRep k 355=0 := by
  change a k 59*walk k 17 [18, 9, 41, 44]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_232 (a k) (relation_zero k) (e k 17)
lemma arrow_span_355 (b : Fin 75) : a k b*normalRep k 355 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_355_57 k]
      exact normal_mem k 475
    · rw [extension_355_58 k]
      exact normal_mem k 476
    · rw [extension_355_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 355=0 from arrow_incompatible k b 17 39 [18, 9, 41, 44] (normal_endpoints 355) h]
    exact Submodule.zero_mem _
lemma extension_356_1 : a k 1*normalRep k 356=normalRep k 476 := by
  change a k 1*walk k 17 [19, 53, 54, 15]=walk k 17 [18, 9, 41, 44, 58]
  rw [← walk_snoc]
  exact Universal.mul_reduced_230 (a k) (relation_zero k) (e k 17)
lemma arrow_span_356 (b : Fin 75) : a k b*normalRep k 356 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_356_1 k]
      exact normal_mem k 476
  · rw [show a k b*normalRep k 356=0 from arrow_incompatible k b 17 1 [19, 53, 54, 15] (normal_endpoints 356) h]
    exact Submodule.zero_mem _
lemma arrow_span_357 (b : Fin 75) : a k b*normalRep k 357 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 357=0 from arrow_incompatible k b 18 46 [20, 30, 2, 0] (normal_endpoints 357) h]
    exact Submodule.zero_mem _
lemma extension_358_24 : a k 24*normalRep k 358=normalRep k 477 := by
  exact (walk_snoc k 18 [21, 69, 8, 66] 24).symm
lemma extension_358_25 : a k 25*normalRep k 358=normalRep k 478 := by
  exact (walk_snoc k 18 [21, 69, 8, 66] 25).symm
lemma arrow_span_358 (b : Fin 75) : a k b*normalRep k 358 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_358_24 k]
      exact normal_mem k 477
    · rw [extension_358_25 k]
      exact normal_mem k 478
  · rw [show a k b*normalRep k 358=0 from arrow_incompatible k b 18 20 [21, 69, 8, 66] (normal_endpoints 358) h]
    exact Submodule.zero_mem _
lemma extension_359_39 : a k 39*normalRep k 359=0 := by
  change a k 39*walk k 18 [21, 69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_212 (a k) (relation_zero k) (e k 18)
lemma extension_359_40 : a k 40*normalRep k 359=(-normalRep k 478) := by
  change a k 40*walk k 18 [21, 69, 8, 68]=(-walk k 18 [21, 69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_301 (a k) (relation_zero k) (e k 18)
lemma arrow_span_359 (b : Fin 75) : a k b*normalRep k 359 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_359_39 k]
      exact Submodule.zero_mem _
    · rw [extension_359_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 478)
  · rw [show a k b*normalRep k 359=0 from arrow_incompatible k b 18 30 [21, 69, 8, 68] (normal_endpoints 359) h]
    exact Submodule.zero_mem _
lemma extension_360_4 : a k 4*normalRep k 360=normalRep k 479 := by
  exact (walk_snoc k 19 [22, 3, 40, 60] 4).symm
lemma arrow_span_360 (b : Fin 75) : a k b*normalRep k 360 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_360_4 k]
      exact normal_mem k 479
  · rw [show a k b*normalRep k 360=0 from arrow_incompatible k b 19 4 [22, 3, 40, 60] (normal_endpoints 360) h]
    exact Submodule.zero_mem _
lemma extension_361_52 : a k 52*normalRep k 361=normalRep k 480 := by
  exact (walk_snoc k 19 [22, 3, 40, 62] 52).symm
lemma extension_361_53 : a k 53*normalRep k 361=normalRep k 479 := by
  change a k 53*walk k 19 [22, 3, 40, 62]=walk k 19 [22, 3, 40, 60, 4]
  rw [← walk_snoc]
  exact Universal.mul_reduced_293 (a k) (relation_zero k) (e k 19)
lemma arrow_span_361 (b : Fin 75) : a k b*normalRep k 361 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_361_52 k]
      exact normal_mem k 480
    · rw [extension_361_53 k]
      exact normal_mem k 479
  · rw [show a k b*normalRep k 361=0 from arrow_incompatible k b 19 37 [22, 3, 40, 62] (normal_endpoints 361) h]
    exact Submodule.zero_mem _
lemma extension_362_9 : a k 9*normalRep k 362=normalRep k 480 := by
  change a k 9*walk k 19 [23, 66, 24, 18]=walk k 19 [22, 3, 40, 62, 52]
  rw [← walk_snoc]
  exact Universal.mul_reduced_238 (a k) (relation_zero k) (e k 19)
lemma arrow_span_362 (b : Fin 75) : a k b*normalRep k 362 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_362_9 k]
      exact normal_mem k 480
  · rw [show a k b*normalRep k 362=0 from arrow_incompatible k b 19 9 [23, 66, 24, 18] (normal_endpoints 362) h]
    exact Submodule.zero_mem _
lemma extension_363_43 : a k 43*normalRep k 363=0 := by
  change a k 43*walk k 20 [24, 18, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_218 (a k) (relation_zero k) (e k 20)
lemma extension_363_44 : a k 44*normalRep k 363=normalRep k 481 := by
  exact (walk_snoc k 20 [24, 18, 9, 41] 44).symm
lemma arrow_span_363 (b : Fin 75) : a k b*normalRep k 363 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_363_43 k]
      exact Submodule.zero_mem _
    · rw [extension_363_44 k]
      exact normal_mem k 481
  · rw [show a k b*normalRep k 363=0 from arrow_incompatible k b 20 32 [24, 18, 9, 41] (normal_endpoints 363) h]
    exact Submodule.zero_mem _
lemma extension_364_15 : a k 15*normalRep k 364=normalRep k 482 := by
  exact (walk_snoc k 20 [24, 19, 53, 54] 15).symm
lemma extension_364_16 : a k 16*normalRep k 364=normalRep k 481 := by
  change a k 16*walk k 20 [24, 19, 53, 54]=walk k 20 [24, 18, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_282 (a k) (relation_zero k) (e k 20)
lemma arrow_span_364 (b : Fin 75) : a k b*normalRep k 364 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_364_15 k]
      exact normal_mem k 482
    · rw [extension_364_16 k]
      exact normal_mem k 481
  · rw [show a k b*normalRep k 364=0 from arrow_incompatible k b 20 15 [24, 19, 53, 54] (normal_endpoints 364) h]
    exact Submodule.zero_mem _
lemma extension_365_32 : a k 32*normalRep k 365=normalRep k 483 := by
  exact (walk_snoc k 21 [26, 31, 73, 67] 32).symm
lemma arrow_span_365 (b : Fin 75) : a k b*normalRep k 365 ∈ normalSpan k := by
  by_cases h : arrowSource b=25
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [32] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_365_32 k]
      exact normal_mem k 483
  · rw [show a k b*normalRep k 365=0 from arrow_incompatible k b 21 25 [26, 31, 73, 67] (normal_endpoints 365) h]
    exact Submodule.zero_mem _
lemma extension_366_39 : a k 39*normalRep k 366=normalRep k 484 := by
  exact (walk_snoc k 21 [26, 31, 73, 68] 39).symm
lemma extension_366_40 : a k 40*normalRep k 366=normalRep k 483 := by
  change a k 40*walk k 21 [26, 31, 73, 68]=walk k 21 [26, 31, 73, 67, 32]
  rw [← walk_snoc]
  exact Universal.mul_reduced_302 (a k) (relation_zero k) (e k 21)
lemma arrow_span_366 (b : Fin 75) : a k b*normalRep k 366 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_366_39 k]
      exact normal_mem k 484
    · rw [extension_366_40 k]
      exact normal_mem k 483
  · rw [show a k b*normalRep k 366=0 from arrow_incompatible k b 21 30 [26, 31, 73, 68] (normal_endpoints 366) h]
    exact Submodule.zero_mem _
lemma extension_367_49 : a k 49*normalRep k 367=normalRep k 485 := by
  exact (walk_snoc k 22 [27, 58, 33, 13] 49).symm
lemma arrow_span_367 (b : Fin 75) : a k b*normalRep k 367 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_367_49 k]
      exact normal_mem k 485
  · rw [show a k b*normalRep k 367=0 from arrow_incompatible k b 22 35 [27, 58, 33, 13] (normal_endpoints 367) h]
    exact Submodule.zero_mem _
lemma extension_368_20 : a k 20*normalRep k 368=0 := by
  change a k 20*walk k 22 [27, 58, 34, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_234 (a k) (relation_zero k) (e k 22)
lemma extension_368_21 : a k 21*normalRep k 368=normalRep k 486 := by
  exact (walk_snoc k 22 [27, 58, 34, 63] 21).symm
lemma arrow_span_368 (b : Fin 75) : a k b*normalRep k 368 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_368_20 k]
      exact Submodule.zero_mem _
    · rw [extension_368_21 k]
      exact normal_mem k 486
  · rw [show a k b*normalRep k 368=0 from arrow_incompatible k b 22 18 [27, 58, 34, 63] (normal_endpoints 368) h]
    exact Submodule.zero_mem _
lemma extension_369_36 : a k 36*normalRep k 369=normalRep k 486 + normalRep k 485 := by
  change a k 36*walk k 22 [27, 58, 34, 64]=walk k 22 [27, 58, 34, 63, 21] + walk k 22 [27, 58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_297 (a k) (relation_zero k) (e k 22)
lemma arrow_span_369 (b : Fin 75) : a k b*normalRep k 369 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_369_36 k]
      exact (normalSpan k).add_mem (normal_mem k 486) (normal_mem k 485)
  · rw [show a k b*normalRep k 369=0 from arrow_incompatible k b 22 28 [27, 58, 34, 64] (normal_endpoints 369) h]
    exact Submodule.zero_mem _
lemma extension_370_43 : a k 43*normalRep k 370=0 := by
  change a k 43*walk k 23 [28, 14, 9, 41]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_265 (a k) (relation_zero k) (e k 23)
lemma extension_370_44 : a k 44*normalRep k 370=normalRep k 487 := by
  exact (walk_snoc k 23 [28, 14, 9, 41] 44).symm
lemma arrow_span_370 (b : Fin 75) : a k b*normalRep k 370 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_370_43 k]
      exact Submodule.zero_mem _
    · rw [extension_370_44 k]
      exact normal_mem k 487
  · rw [show a k b*normalRep k 370=0 from arrow_incompatible k b 23 32 [28, 14, 9, 41] (normal_endpoints 370) h]
    exact Submodule.zero_mem _
lemma extension_371_15 : a k 15*normalRep k 371=normalRep k 488 := by
  exact (walk_snoc k 23 [29, 19, 53, 54] 15).symm
lemma extension_371_16 : a k 16*normalRep k 371=normalRep k 487 := by
  change a k 16*walk k 23 [29, 19, 53, 54]=walk k 23 [28, 14, 9, 41, 44]
  rw [← walk_snoc]
  exact Universal.mul_reduced_283 (a k) (relation_zero k) (e k 23)
lemma arrow_span_371 (b : Fin 75) : a k b*normalRep k 371 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_371_15 k]
      exact normal_mem k 488
    · rw [extension_371_16 k]
      exact normal_mem k 487
  · rw [show a k b*normalRep k 371=0 from arrow_incompatible k b 23 15 [29, 19, 53, 54] (normal_endpoints 371) h]
    exact Submodule.zero_mem _
lemma extension_372_60 : a k 60*normalRep k 372=0 := by
  change a k 60*walk k 24 [31, 73, 67, 32]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_256 (a k) (relation_zero k) (e k 24)
lemma extension_372_61 : a k 61*normalRep k 372=normalRep k 489 := by
  exact (walk_snoc k 24 [31, 73, 67, 32] 61).symm
lemma extension_372_62 : a k 62*normalRep k 372=normalRep k 490 := by
  exact (walk_snoc k 24 [31, 73, 67, 32] 62).symm
lemma arrow_span_372 (b : Fin 75) : a k b*normalRep k 372 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_372_60 k]
      exact Submodule.zero_mem _
    · rw [extension_372_61 k]
      exact normal_mem k 489
    · rw [extension_372_62 k]
      exact normal_mem k 490
  · rw [show a k b*normalRep k 372=0 from arrow_incompatible k b 24 40 [31, 73, 67, 32] (normal_endpoints 372) h]
    exact Submodule.zero_mem _
lemma extension_373_12 : a k 12*normalRep k 373=normalRep k 489 := by
  change a k 12*walk k 24 [31, 73, 68, 39]=walk k 24 [31, 73, 67, 32, 61]
  rw [← walk_snoc]
  exact Universal.mul_reduced_264 (a k) (relation_zero k) (e k 24)
lemma arrow_span_373 (b : Fin 75) : a k b*normalRep k 373 ∈ normalSpan k := by
  by_cases h : arrowSource b=12
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [12] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_373_12 k]
      exact normal_mem k 489
  · rw [show a k b*normalRep k 373=0 from arrow_incompatible k b 24 12 [31, 73, 68, 39] (normal_endpoints 373) h]
    exact Submodule.zero_mem _
lemma extension_374_27 : a k 27*normalRep k 374=normalRep k 491 := by
  exact (walk_snoc k 25 [32, 61, 35, 55] 27).symm
lemma arrow_span_374 (b : Fin 75) : a k b*normalRep k 374 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_374_27 k]
      exact normal_mem k 491
  · rw [show a k b*normalRep k 374=0 from arrow_incompatible k b 25 22 [32, 61, 35, 55] (normal_endpoints 374) h]
    exact Submodule.zero_mem _
lemma extension_375_43 : a k 43*normalRep k 375=normalRep k 492 := by
  exact (walk_snoc k 25 [32, 61, 35, 56] 43).symm
lemma extension_375_44 : a k 44*normalRep k 375=normalRep k 491 := by
  change a k 44*walk k 25 [32, 61, 35, 56]=walk k 25 [32, 61, 35, 55, 27]
  rw [← walk_snoc]
  exact Universal.mul_reduced_284 (a k) (relation_zero k) (e k 25)
lemma arrow_span_375 (b : Fin 75) : a k b*normalRep k 375 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_375_43 k]
      exact normal_mem k 492
    · rw [extension_375_44 k]
      exact normal_mem k 491
  · rw [show a k b*normalRep k 375=0 from arrow_incompatible k b 25 32 [32, 61, 35, 56] (normal_endpoints 375) h]
    exact Submodule.zero_mem _
lemma extension_376_45 : a k 45*normalRep k 376=normalRep k 493 := by
  exact (walk_snoc k 25 [32, 62, 52, 42] 45).symm
lemma extension_376_46 : a k 46*normalRep k 376=normalRep k 492 := by
  change a k 46*walk k 25 [32, 62, 52, 42]=walk k 25 [32, 61, 35, 56, 43]
  rw [← walk_snoc]
  exact Universal.mul_reduced_266 (a k) (relation_zero k) (e k 25)
lemma arrow_span_376 (b : Fin 75) : a k b*normalRep k 376 ∈ normalSpan k := by
  by_cases h : arrowSource b=33
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [45, 46] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_376_45 k]
      exact normal_mem k 493
    · rw [extension_376_46 k]
      exact normal_mem k 492
  · rw [show a k b*normalRep k 376=0 from arrow_incompatible k b 25 33 [32, 62, 52, 42] (normal_endpoints 376) h]
    exact Submodule.zero_mem _
lemma extension_377_8 : a k 8*normalRep k 377=normalRep k 494 := by
  exact (walk_snoc k 26 [33, 13, 49, 69] 8).symm
lemma arrow_span_377 (b : Fin 75) : a k b*normalRep k 377 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_377_8 k]
      exact normal_mem k 494
  · rw [show a k b*normalRep k 377=0 from arrow_incompatible k b 26 8 [33, 13, 49, 69] (normal_endpoints 377) h]
    exact Submodule.zero_mem _
lemma extension_378_72 : a k 72*normalRep k 378=normalRep k 495 := by
  exact (walk_snoc k 26 [33, 13, 49, 71] 72).symm
lemma extension_378_73 : a k 73*normalRep k 378=normalRep k 494 := by
  change a k 73*walk k 26 [33, 13, 49, 71]=walk k 26 [33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_306 (a k) (relation_zero k) (e k 26)
lemma arrow_span_378 (b : Fin 75) : a k b*normalRep k 378 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_378_72 k]
      exact normal_mem k 495
    · rw [extension_378_73 k]
      exact normal_mem k 494
  · rw [show a k b*normalRep k 378=0 from arrow_incompatible k b 26 44 [33, 13, 49, 71] (normal_endpoints 378) h]
    exact Submodule.zero_mem _
lemma extension_379_2 : a k 2*normalRep k 379=normalRep k 496 := by
  exact (walk_snoc k 26 [34, 63, 20, 30] 2).symm
lemma arrow_span_379 (b : Fin 75) : a k b*normalRep k 379 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_379_2 k]
      exact normal_mem k 496
  · rw [show a k b*normalRep k 379=0 from arrow_incompatible k b 26 2 [34, 63, 20, 30] (normal_endpoints 379) h]
    exact Submodule.zero_mem _
lemma extension_380_22 : a k 22*normalRep k 380=normalRep k 497 := by
  exact (walk_snoc k 26 [34, 63, 21, 70] 22).symm
lemma extension_380_23 : a k 23*normalRep k 380=normalRep k 494 := by
  change a k 23*walk k 26 [34, 63, 21, 70]=walk k 26 [33, 13, 49, 69, 8]
  rw [← walk_snoc]
  exact Universal.mul_reduced_307 (a k) (relation_zero k) (e k 26)
lemma arrow_span_380 (b : Fin 75) : a k b*normalRep k 380 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_380_22 k]
      exact normal_mem k 497
    · rw [extension_380_23 k]
      exact normal_mem k 494
  · rw [show a k b*normalRep k 380=0 from arrow_incompatible k b 26 19 [34, 63, 21, 70] (normal_endpoints 380) h]
    exact Submodule.zero_mem _
lemma extension_381_33 : a k 33*normalRep k 381=normalRep k 498 := by
  exact (walk_snoc k 27 [35, 55, 27, 58] 33).symm
lemma extension_381_34 : a k 34*normalRep k 381=normalRep k 499 := by
  exact (walk_snoc k 27 [35, 55, 27, 58] 34).symm
lemma arrow_span_381 (b : Fin 75) : a k b*normalRep k 381 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_381_33 k]
      exact normal_mem k 498
    · rw [extension_381_34 k]
      exact normal_mem k 499
  · rw [show a k b*normalRep k 381=0 from arrow_incompatible k b 27 26 [35, 55, 27, 58] (normal_endpoints 381) h]
    exact Submodule.zero_mem _
lemma extension_382_50 : a k 50*normalRep k 382=normalRep k 500 := by
  exact (walk_snoc k 27 [35, 55, 27, 59] 50).symm
lemma extension_382_51 : a k 51*normalRep k 382=normalRep k 499 := by
  change a k 51*walk k 27 [35, 55, 27, 59]=walk k 27 [35, 55, 27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_289 (a k) (relation_zero k) (e k 27)
lemma arrow_span_382 (b : Fin 75) : a k b*normalRep k 382 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_382_50 k]
      exact normal_mem k 500
    · rw [extension_382_51 k]
      exact normal_mem k 499
  · rw [show a k b*normalRep k 382=0 from arrow_incompatible k b 27 36 [35, 55, 27, 59] (normal_endpoints 382) h]
    exact Submodule.zero_mem _
lemma extension_383_7 : a k 7*normalRep k 383=normalRep k 500 := by
  change a k 7*walk k 27 [35, 56, 43, 47]=walk k 27 [35, 55, 27, 59, 50]
  rw [← walk_snoc]
  exact Universal.mul_reduced_272 (a k) (relation_zero k) (e k 27)
lemma arrow_span_383 (b : Fin 75) : a k b*normalRep k 383 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_383_7 k]
      exact normal_mem k 500
  · rw [show a k b*normalRep k 383=0 from arrow_incompatible k b 27 7 [35, 56, 43, 47] (normal_endpoints 383) h]
    exact Submodule.zero_mem _
lemma extension_384_39 : a k 39*normalRep k 384=0 := by
  change a k 39*walk k 28 [36, 70, 22, 3]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_213 (a k) (relation_zero k) (e k 28)
lemma extension_384_40 : a k 40*normalRep k 384=normalRep k 501 := by
  exact (walk_snoc k 28 [36, 70, 22, 3] 40).symm
lemma arrow_span_384 (b : Fin 75) : a k b*normalRep k 384 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_384_39 k]
      exact Submodule.zero_mem _
    · rw [extension_384_40 k]
      exact normal_mem k 501
  · rw [show a k b*normalRep k 384=0 from arrow_incompatible k b 28 30 [36, 70, 22, 3] (normal_endpoints 384) h]
    exact Submodule.zero_mem _
lemma extension_385_24 : a k 24*normalRep k 385=normalRep k 502 := by
  exact (walk_snoc k 28 [36, 70, 23, 66] 24).symm
lemma extension_385_25 : a k 25*normalRep k 385=normalRep k 501 := by
  change a k 25*walk k 28 [36, 70, 23, 66]=walk k 28 [36, 70, 22, 3, 40]
  rw [← walk_snoc]
  exact Universal.mul_reduced_303 (a k) (relation_zero k) (e k 28)
lemma arrow_span_385 (b : Fin 75) : a k b*normalRep k 385 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_385_24 k]
      exact normal_mem k 502
    · rw [extension_385_25 k]
      exact normal_mem k 501
  · rw [show a k b*normalRep k 385=0 from arrow_incompatible k b 28 20 [36, 70, 23, 66] (normal_endpoints 385) h]
    exact Submodule.zero_mem _
lemma extension_386_28 : a k 28*normalRep k 386=normalRep k 503 := by
  exact (walk_snoc k 28 [36, 71, 72, 38] 28).symm
lemma extension_386_29 : a k 29*normalRep k 386=normalRep k 502 := by
  change a k 29*walk k 28 [36, 71, 72, 38]=walk k 28 [36, 70, 23, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_262 (a k) (relation_zero k) (e k 28)
lemma arrow_span_386 (b : Fin 75) : a k b*normalRep k 386 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_386_28 k]
      exact normal_mem k 503
    · rw [extension_386_29 k]
      exact normal_mem k 502
  · rw [show a k b*normalRep k 386=0 from arrow_incompatible k b 28 23 [36, 71, 72, 38] (normal_endpoints 386) h]
    exact Submodule.zero_mem _
lemma extension_387_41 : a k 41*normalRep k 387=normalRep k 504 := by
  exact (walk_snoc k 29 [37, 24, 18, 9] 41).symm
lemma extension_387_42 : a k 42*normalRep k 387=0 := by
  change a k 42*walk k 29 [37, 24, 18, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_228 (a k) (relation_zero k) (e k 29)
lemma arrow_span_387 (b : Fin 75) : a k b*normalRep k 387 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_387_41 k]
      exact normal_mem k 504
    · rw [extension_387_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 387=0 from arrow_incompatible k b 29 31 [37, 24, 18, 9] (normal_endpoints 387) h]
    exact Submodule.zero_mem _
lemma extension_388_54 : a k 54*normalRep k 388=normalRep k 505 := by
  exact (walk_snoc k 29 [37, 24, 19, 53] 54).symm
lemma extension_388_55 : a k 55*normalRep k 388=0 := by
  change a k 55*walk k 29 [37, 24, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_216 (a k) (relation_zero k) (e k 29)
lemma extension_388_56 : a k 56*normalRep k 388=normalRep k 504 := by
  change a k 56*walk k 29 [37, 24, 19, 53]=walk k 29 [37, 24, 18, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_279 (a k) (relation_zero k) (e k 29)
lemma arrow_span_388 (b : Fin 75) : a k b*normalRep k 388 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_388_54 k]
      exact normal_mem k 505
    · rw [extension_388_55 k]
      exact Submodule.zero_mem _
    · rw [extension_388_56 k]
      exact normal_mem k 504
  · rw [show a k b*normalRep k 388=0 from arrow_incompatible k b 29 38 [37, 24, 19, 53] (normal_endpoints 388) h]
    exact Submodule.zero_mem _
lemma extension_389_27 : a k 27*normalRep k 389=normalRep k 506 := by
  exact (walk_snoc k 30 [39, 12, 35, 55] 27).symm
lemma arrow_span_389 (b : Fin 75) : a k b*normalRep k 389 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_389_27 k]
      exact normal_mem k 506
  · rw [show a k b*normalRep k 389=0 from arrow_incompatible k b 30 22 [39, 12, 35, 55] (normal_endpoints 389) h]
    exact Submodule.zero_mem _
lemma extension_390_43 : a k 43*normalRep k 390=normalRep k 507 := by
  exact (walk_snoc k 30 [39, 12, 35, 56] 43).symm
lemma extension_390_44 : a k 44*normalRep k 390=normalRep k 506 := by
  change a k 44*walk k 30 [39, 12, 35, 56]=walk k 30 [39, 12, 35, 55, 27]
  rw [← walk_snoc]
  exact Universal.mul_reduced_285 (a k) (relation_zero k) (e k 30)
lemma arrow_span_390 (b : Fin 75) : a k b*normalRep k 390 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_390_43 k]
      exact normal_mem k 507
    · rw [extension_390_44 k]
      exact normal_mem k 506
  · rw [show a k b*normalRep k 390=0 from arrow_incompatible k b 30 32 [39, 12, 35, 56] (normal_endpoints 390) h]
    exact Submodule.zero_mem _
lemma extension_391_15 : a k 15*normalRep k 391=normalRep k 508 := by
  exact (walk_snoc k 30 [40, 60, 4, 54] 15).symm
lemma extension_391_16 : a k 16*normalRep k 391=normalRep k 509 := by
  exact (walk_snoc k 30 [40, 60, 4, 54] 16).symm
lemma arrow_span_391 (b : Fin 75) : a k b*normalRep k 391 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_391_15 k]
      exact normal_mem k 508
    · rw [extension_391_16 k]
      exact normal_mem k 509
  · rw [show a k b*normalRep k 391=0 from arrow_incompatible k b 30 15 [40, 60, 4, 54] (normal_endpoints 391) h]
    exact Submodule.zero_mem _
lemma extension_392_43 : a k 43*normalRep k 392=0 := by
  change a k 43*walk k 30 [40, 60, 4, 56]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_219 (a k) (relation_zero k) (e k 30)
lemma extension_392_44 : a k 44*normalRep k 392=normalRep k 509 := by
  change a k 44*walk k 30 [40, 60, 4, 56]=walk k 30 [40, 60, 4, 54, 16]
  rw [← walk_snoc]
  exact Universal.mul_reduced_286 (a k) (relation_zero k) (e k 30)
lemma arrow_span_392 (b : Fin 75) : a k b*normalRep k 392 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_392_43 k]
      exact Submodule.zero_mem _
    · rw [extension_392_44 k]
      exact normal_mem k 509
  · rw [show a k b*normalRep k 392=0 from arrow_incompatible k b 30 32 [40, 60, 4, 56] (normal_endpoints 392) h]
    exact Submodule.zero_mem _
lemma extension_393_45 : a k 45*normalRep k 393=normalRep k 510 := by
  exact (walk_snoc k 30 [40, 62, 52, 42] 45).symm
lemma extension_393_46 : a k 46*normalRep k 393=normalRep k 507 := by
  change a k 46*walk k 30 [40, 62, 52, 42]=walk k 30 [39, 12, 35, 56, 43]
  rw [← walk_snoc]
  exact Universal.mul_reduced_267 (a k) (relation_zero k) (e k 30)
lemma arrow_span_393 (b : Fin 75) : a k b*normalRep k 393 ∈ normalSpan k := by
  by_cases h : arrowSource b=33
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [45, 46] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_393_45 k]
      exact normal_mem k 510
    · rw [extension_393_46 k]
      exact normal_mem k 507
  · rw [show a k b*normalRep k 393=0 from arrow_incompatible k b 30 33 [40, 62, 52, 42] (normal_endpoints 393) h]
    exact Submodule.zero_mem _
lemma extension_394_17 : a k 17*normalRep k 394=normalRep k 511 := by
  exact (walk_snoc k 31 [41, 43, 47, 7] 17).symm
lemma arrow_span_394 (b : Fin 75) : a k b*normalRep k 394 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_394_17 k]
      exact normal_mem k 511
  · rw [show a k b*normalRep k 394=0 from arrow_incompatible k b 31 16 [41, 43, 47, 7] (normal_endpoints 394) h]
    exact Submodule.zero_mem _
lemma extension_395_63 : a k 63*normalRep k 395=normalRep k 511 := by
  change a k 63*walk k 31 [41, 43, 48, 51]=walk k 31 [41, 43, 47, 7, 17]
  rw [← walk_snoc]
  exact Universal.mul_reduced_276 (a k) (relation_zero k) (e k 31)
lemma extension_395_64 : a k 64*normalRep k 395=normalRep k 512 := by
  exact (walk_snoc k 31 [41, 43, 48, 51] 64).symm
lemma extension_395_65 : a k 65*normalRep k 395=normalRep k 513 := by
  exact (walk_snoc k 31 [41, 43, 48, 51] 65).symm
lemma arrow_span_395 (b : Fin 75) : a k b*normalRep k 395 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_395_63 k]
      exact normal_mem k 511
    · rw [extension_395_64 k]
      exact normal_mem k 512
    · rw [extension_395_65 k]
      exact normal_mem k 513
  · rw [show a k b*normalRep k 395=0 from arrow_incompatible k b 31 41 [41, 43, 48, 51] (normal_endpoints 395) h]
    exact Submodule.zero_mem _
lemma extension_396_63 : a k 63*normalRep k 396=normalRep k 514 := by
  exact (walk_snoc k 31 [41, 44, 57, 5] 63).symm
lemma extension_396_64 : a k 64*normalRep k 396=0 := by
  change a k 64*walk k 31 [41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_220 (a k) (relation_zero k) (e k 31)
lemma extension_396_65 : a k 65*normalRep k 396=0 := by
  change a k 65*walk k 31 [41, 44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_221 (a k) (relation_zero k) (e k 31)
lemma arrow_span_396 (b : Fin 75) : a k b*normalRep k 396 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_396_63 k]
      exact normal_mem k 514
    · rw [extension_396_64 k]
      exact Submodule.zero_mem _
    · rw [extension_396_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 396=0 from arrow_incompatible k b 31 41 [41, 44, 57, 5] (normal_endpoints 396) h]
    exact Submodule.zero_mem _
lemma extension_397_13 : a k 13*normalRep k 397=normalRep k 513 := by
  change a k 13*walk k 31 [41, 44, 58, 33]=walk k 31 [41, 43, 48, 51, 65]
  rw [← walk_snoc]
  exact Universal.mul_reduced_257 (a k) (relation_zero k) (e k 31)
lemma arrow_span_397 (b : Fin 75) : a k b*normalRep k 397 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_397_13 k]
      exact normal_mem k 513
  · rw [show a k b*normalRep k 397=0 from arrow_incompatible k b 31 13 [41, 44, 58, 33] (normal_endpoints 397) h]
    exact Submodule.zero_mem _
lemma extension_398_20 : a k 20*normalRep k 398=0 := by
  change a k 20*walk k 32 [43, 47, 7, 17]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_235 (a k) (relation_zero k) (e k 32)
lemma extension_398_21 : a k 21*normalRep k 398=normalRep k 515 := by
  exact (walk_snoc k 32 [43, 47, 7, 17] 21).symm
lemma arrow_span_398 (b : Fin 75) : a k b*normalRep k 398 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_398_20 k]
      exact Submodule.zero_mem _
    · rw [extension_398_21 k]
      exact normal_mem k 515
  · rw [show a k b*normalRep k 398=0 from arrow_incompatible k b 32 18 [43, 47, 7, 17] (normal_endpoints 398) h]
    exact Submodule.zero_mem _
lemma extension_399_36 : a k 36*normalRep k 399=normalRep k 516 := by
  exact (walk_snoc k 32 [43, 48, 51, 64] 36).symm
lemma arrow_span_399 (b : Fin 75) : a k b*normalRep k 399 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_399_36 k]
      exact normal_mem k 516
  · rw [show a k b*normalRep k 399=0 from arrow_incompatible k b 32 28 [43, 48, 51, 64] (normal_endpoints 399) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
