import N6NormalData
import N6Reduced1
import N6Reduced2
import N6Reduced3
import N6Reduced4
import N6Reduced5
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_300_50 : a k 50*normalRep k 300=normalRep k 421 := by
  exact (walk_snoc k 38 [55, 27, 59] 50).symm
lemma extension_300_51 : a k 51*normalRep k 300=normalRep k 420 := by
  change a k 51*walk k 38 [55, 27, 59]=walk k 38 [55, 27, 58, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_190 (a k) (relation_zero k) (e k 38)
lemma arrow_span_300 (b : Fin 75) : a k b*normalRep k 300 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_300_50 k]
      exact normal_mem k 421
    · rw [extension_300_51 k]
      exact normal_mem k 420
  · rw [show a k b*normalRep k 300=0 from arrow_incompatible k b 38 36 [55, 27, 59] (normal_endpoints 300) h]
    exact Submodule.zero_mem _
lemma extension_301_7 : a k 7*normalRep k 301=normalRep k 421 := by
  change a k 7*walk k 38 [56, 43, 47]=walk k 38 [55, 27, 59, 50]
  rw [← walk_snoc]
  exact Universal.mul_reduced_174 (a k) (relation_zero k) (e k 38)
lemma arrow_span_301 (b : Fin 75) : a k b*normalRep k 301 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_301_7 k]
      exact normal_mem k 421
  · rw [show a k b*normalRep k 301=0 from arrow_incompatible k b 38 7 [56, 43, 47] (normal_endpoints 301) h]
    exact Submodule.zero_mem _
lemma extension_302_20 : a k 20*normalRep k 302=normalRep k 422 := by
  exact (walk_snoc k 39 [57, 5, 63] 20).symm
lemma extension_302_21 : a k 21*normalRep k 302=0 := by
  change a k 21*walk k 39 [57, 5, 63]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_197 (a k) (relation_zero k) (e k 39)
lemma arrow_span_302 (b : Fin 75) : a k b*normalRep k 302 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_302_20 k]
      exact normal_mem k 422
    · rw [extension_302_21 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 302=0 from arrow_incompatible k b 39 18 [57, 5, 63] (normal_endpoints 302) h]
    exact Submodule.zero_mem _
lemma extension_303_49 : a k 49*normalRep k 303=normalRep k 423 := by
  exact (walk_snoc k 39 [58, 33, 13] 49).symm
lemma arrow_span_303 (b : Fin 75) : a k b*normalRep k 303 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_303_49 k]
      exact normal_mem k 423
  · rw [show a k b*normalRep k 303=0 from arrow_incompatible k b 39 35 [58, 33, 13] (normal_endpoints 303) h]
    exact Submodule.zero_mem _
lemma extension_304_20 : a k 20*normalRep k 304=normalRep k 422 := by
  change a k 20*walk k 39 [58, 34, 63]=walk k 39 [57, 5, 63, 20]
  rw [← walk_snoc]
  exact Universal.mul_reduced_134 (a k) (relation_zero k) (e k 39)
lemma extension_304_21 : a k 21*normalRep k 304=normalRep k 424 := by
  exact (walk_snoc k 39 [58, 34, 63] 21).symm
lemma arrow_span_304 (b : Fin 75) : a k b*normalRep k 304 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_304_20 k]
      exact normal_mem k 422
    · rw [extension_304_21 k]
      exact normal_mem k 424
  · rw [show a k b*normalRep k 304=0 from arrow_incompatible k b 39 18 [58, 34, 63] (normal_endpoints 304) h]
    exact Submodule.zero_mem _
lemma extension_305_36 : a k 36*normalRep k 305=normalRep k 424 + normalRep k 423 := by
  change a k 36*walk k 39 [58, 34, 64]=walk k 39 [58, 34, 63, 21] + walk k 39 [58, 33, 13, 49]
  rw [← walk_snoc]
  exact Universal.mul_reduced_198 (a k) (relation_zero k) (e k 39)
lemma arrow_span_305 (b : Fin 75) : a k b*normalRep k 305 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_305_36 k]
      exact (normalSpan k).add_mem (normal_mem k 424) (normal_mem k 423)
  · rw [show a k b*normalRep k 305=0 from arrow_incompatible k b 39 28 [58, 34, 64] (normal_endpoints 305) h]
    exact Submodule.zero_mem _
lemma extension_306_15 : a k 15*normalRep k 306=normalRep k 425 := by
  exact (walk_snoc k 40 [60, 4, 54] 15).symm
lemma extension_306_16 : a k 16*normalRep k 306=normalRep k 426 := by
  exact (walk_snoc k 40 [60, 4, 54] 16).symm
lemma arrow_span_306 (b : Fin 75) : a k b*normalRep k 306 ∈ normalSpan k := by
  by_cases h : arrowSource b=15
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [15, 16] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_306_15 k]
      exact normal_mem k 425
    · rw [extension_306_16 k]
      exact normal_mem k 426
  · rw [show a k b*normalRep k 306=0 from arrow_incompatible k b 40 15 [60, 4, 54] (normal_endpoints 306) h]
    exact Submodule.zero_mem _
lemma extension_307_43 : a k 43*normalRep k 307=0 := by
  change a k 43*walk k 40 [60, 4, 56]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_119 (a k) (relation_zero k) (e k 40)
lemma extension_307_44 : a k 44*normalRep k 307=normalRep k 426 := by
  change a k 44*walk k 40 [60, 4, 56]=walk k 40 [60, 4, 54, 16]
  rw [← walk_snoc]
  exact Universal.mul_reduced_186 (a k) (relation_zero k) (e k 40)
lemma arrow_span_307 (b : Fin 75) : a k b*normalRep k 307 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_307_43 k]
      exact Submodule.zero_mem _
    · rw [extension_307_44 k]
      exact normal_mem k 426
  · rw [show a k b*normalRep k 307=0 from arrow_incompatible k b 40 32 [60, 4, 56] (normal_endpoints 307) h]
    exact Submodule.zero_mem _
lemma extension_308_27 : a k 27*normalRep k 308=normalRep k 427 := by
  exact (walk_snoc k 40 [61, 35, 55] 27).symm
lemma arrow_span_308 (b : Fin 75) : a k b*normalRep k 308 ∈ normalSpan k := by
  by_cases h : arrowSource b=22
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [27] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_308_27 k]
      exact normal_mem k 427
  · rw [show a k b*normalRep k 308=0 from arrow_incompatible k b 40 22 [61, 35, 55] (normal_endpoints 308) h]
    exact Submodule.zero_mem _
lemma extension_309_43 : a k 43*normalRep k 309=normalRep k 428 := by
  exact (walk_snoc k 40 [61, 35, 56] 43).symm
lemma extension_309_44 : a k 44*normalRep k 309=normalRep k 427 := by
  change a k 44*walk k 40 [61, 35, 56]=walk k 40 [61, 35, 55, 27]
  rw [← walk_snoc]
  exact Universal.mul_reduced_187 (a k) (relation_zero k) (e k 40)
lemma arrow_span_309 (b : Fin 75) : a k b*normalRep k 309 ∈ normalSpan k := by
  by_cases h : arrowSource b=32
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [43, 44] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_309_43 k]
      exact normal_mem k 428
    · rw [extension_309_44 k]
      exact normal_mem k 427
  · rw [show a k b*normalRep k 309=0 from arrow_incompatible k b 40 32 [61, 35, 56] (normal_endpoints 309) h]
    exact Submodule.zero_mem _
lemma extension_310_45 : a k 45*normalRep k 310=normalRep k 429 := by
  exact (walk_snoc k 40 [62, 52, 42] 45).symm
lemma extension_310_46 : a k 46*normalRep k 310=normalRep k 428 := by
  change a k 46*walk k 40 [62, 52, 42]=walk k 40 [61, 35, 56, 43]
  rw [← walk_snoc]
  exact Universal.mul_reduced_168 (a k) (relation_zero k) (e k 40)
lemma arrow_span_310 (b : Fin 75) : a k b*normalRep k 310 ∈ normalSpan k := by
  by_cases h : arrowSource b=33
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [45, 46] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_310_45 k]
      exact normal_mem k 429
    · rw [extension_310_46 k]
      exact normal_mem k 428
  · rw [show a k b*normalRep k 310=0 from arrow_incompatible k b 40 33 [62, 52, 42] (normal_endpoints 310) h]
    exact Submodule.zero_mem _
lemma extension_311_2 : a k 2*normalRep k 311=normalRep k 430 := by
  exact (walk_snoc k 41 [63, 20, 30] 2).symm
lemma arrow_span_311 (b : Fin 75) : a k b*normalRep k 311 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_311_2 k]
      exact normal_mem k 430
  · rw [show a k b*normalRep k 311=0 from arrow_incompatible k b 41 2 [63, 20, 30] (normal_endpoints 311) h]
    exact Submodule.zero_mem _
lemma extension_312_8 : a k 8*normalRep k 312=normalRep k 431 := by
  exact (walk_snoc k 41 [63, 21, 69] 8).symm
lemma arrow_span_312 (b : Fin 75) : a k b*normalRep k 312 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_312_8 k]
      exact normal_mem k 431
  · rw [show a k b*normalRep k 312=0 from arrow_incompatible k b 41 8 [63, 21, 69] (normal_endpoints 312) h]
    exact Submodule.zero_mem _
lemma extension_313_22 : a k 22*normalRep k 313=normalRep k 432 := by
  exact (walk_snoc k 41 [63, 21, 70] 22).symm
lemma extension_313_23 : a k 23*normalRep k 313=(-normalRep k 431) := by
  change a k 23*walk k 41 [63, 21, 70]=(-walk k 41 [63, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_204 (a k) (relation_zero k) (e k 41)
lemma arrow_span_313 (b : Fin 75) : a k b*normalRep k 313 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_313_22 k]
      exact normal_mem k 432
    · rw [extension_313_23 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 431)
  · rw [show a k b*normalRep k 313=0 from arrow_incompatible k b 41 19 [63, 21, 70] (normal_endpoints 313) h]
    exact Submodule.zero_mem _
lemma extension_314_72 : a k 72*normalRep k 314=normalRep k 433 := by
  exact (walk_snoc k 41 [64, 36, 71] 72).symm
lemma extension_314_73 : a k 73*normalRep k 314=(-normalRep k 431) := by
  change a k 73*walk k 41 [64, 36, 71]=(-walk k 41 [63, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_205 (a k) (relation_zero k) (e k 41)
lemma arrow_span_314 (b : Fin 75) : a k b*normalRep k 314 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_314_72 k]
      exact normal_mem k 433
    · rw [extension_314_73 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 431)
  · rw [show a k b*normalRep k 314=0 from arrow_incompatible k b 41 44 [64, 36, 71] (normal_endpoints 314) h]
    exact Submodule.zero_mem _
lemma extension_315_9 : a k 9*normalRep k 315=normalRep k 434 := by
  exact (walk_snoc k 42 [66, 24, 18] 9).symm
lemma arrow_span_315 (b : Fin 75) : a k b*normalRep k 315 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_315_9 k]
      exact normal_mem k 434
  · rw [show a k b*normalRep k 315=0 from arrow_incompatible k b 42 9 [66, 24, 18] (normal_endpoints 315) h]
    exact Submodule.zero_mem _
lemma extension_316_52 : a k 52*normalRep k 316=normalRep k 434 := by
  change a k 52*walk k 42 [66, 24, 19]=walk k 42 [66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_137 (a k) (relation_zero k) (e k 42)
lemma extension_316_53 : a k 53*normalRep k 316=normalRep k 435 := by
  exact (walk_snoc k 42 [66, 24, 19] 53).symm
lemma arrow_span_316 (b : Fin 75) : a k b*normalRep k 316 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_316_52 k]
      exact normal_mem k 434
    · rw [extension_316_53 k]
      exact normal_mem k 435
  · rw [show a k b*normalRep k 316=0 from arrow_incompatible k b 42 37 [66, 24, 19] (normal_endpoints 316) h]
    exact Submodule.zero_mem _
lemma extension_317_4 : a k 4*normalRep k 317=normalRep k 435 := by
  change a k 4*walk k 42 [66, 25, 60]=walk k 42 [66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_193 (a k) (relation_zero k) (e k 42)
lemma arrow_span_317 (b : Fin 75) : a k b*normalRep k 317 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_317_4 k]
      exact normal_mem k 435
  · rw [show a k b*normalRep k 317=0 from arrow_incompatible k b 42 4 [66, 25, 60] (normal_endpoints 317) h]
    exact Submodule.zero_mem _
lemma extension_318_35 : a k 35*normalRep k 318=normalRep k 436 := by
  exact (walk_snoc k 42 [67, 32, 61] 35).symm
lemma arrow_span_318 (b : Fin 75) : a k b*normalRep k 318 ∈ normalSpan k := by
  by_cases h : arrowSource b=27
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [35] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_318_35 k]
      exact normal_mem k 436
  · rw [show a k b*normalRep k 318=0 from arrow_incompatible k b 42 27 [67, 32, 61] (normal_endpoints 318) h]
    exact Submodule.zero_mem _
lemma extension_319_52 : a k 52*normalRep k 319=normalRep k 437 := by
  exact (walk_snoc k 42 [67, 32, 62] 52).symm
lemma extension_319_53 : a k 53*normalRep k 319=normalRep k 436 := by
  change a k 53*walk k 42 [67, 32, 62]=walk k 42 [67, 32, 61, 35]
  rw [← walk_snoc]
  exact Universal.mul_reduced_194 (a k) (relation_zero k) (e k 42)
lemma arrow_span_319 (b : Fin 75) : a k b*normalRep k 319 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_319_52 k]
      exact normal_mem k 437
    · rw [extension_319_53 k]
      exact normal_mem k 436
  · rw [show a k b*normalRep k 319=0 from arrow_incompatible k b 42 37 [67, 32, 62] (normal_endpoints 319) h]
    exact Submodule.zero_mem _
lemma extension_320_24 : a k 24*normalRep k 320=normalRep k 438 := by
  exact (walk_snoc k 43 [69, 8, 66] 24).symm
lemma extension_320_25 : a k 25*normalRep k 320=normalRep k 439 := by
  exact (walk_snoc k 43 [69, 8, 66] 25).symm
lemma arrow_span_320 (b : Fin 75) : a k b*normalRep k 320 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_320_24 k]
      exact normal_mem k 438
    · rw [extension_320_25 k]
      exact normal_mem k 439
  · rw [show a k b*normalRep k 320=0 from arrow_incompatible k b 43 20 [69, 8, 66] (normal_endpoints 320) h]
    exact Submodule.zero_mem _
lemma extension_321_39 : a k 39*normalRep k 321=0 := by
  change a k 39*walk k 43 [69, 8, 68]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_123 (a k) (relation_zero k) (e k 43)
lemma extension_321_40 : a k 40*normalRep k 321=(-normalRep k 439) := by
  change a k 40*walk k 43 [69, 8, 68]=(-walk k 43 [69, 8, 66, 25])
  rw [← walk_snoc]
  exact Universal.mul_reduced_200 (a k) (relation_zero k) (e k 43)
lemma arrow_span_321 (b : Fin 75) : a k b*normalRep k 321 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_321_39 k]
      exact Submodule.zero_mem _
    · rw [extension_321_40 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 439)
  · rw [show a k b*normalRep k 321=0 from arrow_incompatible k b 43 30 [69, 8, 68] (normal_endpoints 321) h]
    exact Submodule.zero_mem _
lemma extension_322_39 : a k 39*normalRep k 322=0 := by
  change a k 39*walk k 43 [70, 22, 3]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_116 (a k) (relation_zero k) (e k 43)
lemma extension_322_40 : a k 40*normalRep k 322=normalRep k 440 := by
  exact (walk_snoc k 43 [70, 22, 3] 40).symm
lemma arrow_span_322 (b : Fin 75) : a k b*normalRep k 322 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_322_39 k]
      exact Submodule.zero_mem _
    · rw [extension_322_40 k]
      exact normal_mem k 440
  · rw [show a k b*normalRep k 322=0 from arrow_incompatible k b 43 30 [70, 22, 3] (normal_endpoints 322) h]
    exact Submodule.zero_mem _
lemma extension_323_24 : a k 24*normalRep k 323=normalRep k 441 := by
  exact (walk_snoc k 43 [70, 23, 66] 24).symm
lemma extension_323_25 : a k 25*normalRep k 323=normalRep k 440 := by
  change a k 25*walk k 43 [70, 23, 66]=walk k 43 [70, 22, 3, 40]
  rw [← walk_snoc]
  exact Universal.mul_reduced_201 (a k) (relation_zero k) (e k 43)
lemma arrow_span_323 (b : Fin 75) : a k b*normalRep k 323 ∈ normalSpan k := by
  by_cases h : arrowSource b=20
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [24, 25] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_323_24 k]
      exact normal_mem k 441
    · rw [extension_323_25 k]
      exact normal_mem k 440
  · rw [show a k b*normalRep k 323=0 from arrow_incompatible k b 43 20 [70, 23, 66] (normal_endpoints 323) h]
    exact Submodule.zero_mem _
lemma extension_324_28 : a k 28*normalRep k 324=normalRep k 442 := by
  exact (walk_snoc k 43 [71, 72, 38] 28).symm
lemma extension_324_29 : a k 29*normalRep k 324=normalRep k 438 + normalRep k 441 := by
  change a k 29*walk k 43 [71, 72, 38]=walk k 43 [69, 8, 66, 24] + walk k 43 [70, 23, 66, 24]
  rw [← walk_snoc]
  exact Universal.mul_reduced_164 (a k) (relation_zero k) (e k 43)
lemma arrow_span_324 (b : Fin 75) : a k b*normalRep k 324 ∈ normalSpan k := by
  by_cases h : arrowSource b=23
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [28, 29] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_324_28 k]
      exact normal_mem k 442
    · rw [extension_324_29 k]
      exact (normalSpan k).add_mem (normal_mem k 438) (normal_mem k 441)
  · rw [show a k b*normalRep k 324=0 from arrow_incompatible k b 43 23 [71, 72, 38] (normal_endpoints 324) h]
    exact Submodule.zero_mem _
lemma extension_325_18 : a k 18*normalRep k 325=normalRep k 443 := by
  exact (walk_snoc k 44 [72, 37, 24] 18).symm
lemma extension_325_19 : a k 19*normalRep k 325=normalRep k 444 := by
  exact (walk_snoc k 44 [72, 37, 24] 19).symm
lemma arrow_span_325 (b : Fin 75) : a k b*normalRep k 325 ∈ normalSpan k := by
  by_cases h : arrowSource b=17
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [18, 19] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_325_18 k]
      exact normal_mem k 443
    · rw [extension_325_19 k]
      exact normal_mem k 444
  · rw [show a k b*normalRep k 325=0 from arrow_incompatible k b 44 17 [72, 37, 24] (normal_endpoints 325) h]
    exact Submodule.zero_mem _
lemma extension_326_60 : a k 60*normalRep k 326=normalRep k 445 := by
  exact (walk_snoc k 44 [72, 37, 25] 60).symm
lemma extension_326_61 : a k 61*normalRep k 326=0 := by
  change a k 61*walk k 44 [72, 37, 25]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_148 (a k) (relation_zero k) (e k 44)
lemma extension_326_62 : a k 62*normalRep k 326=normalRep k 444 := by
  change a k 62*walk k 44 [72, 37, 25]=walk k 44 [72, 37, 24, 19]
  rw [← walk_snoc]
  exact Universal.mul_reduced_151 (a k) (relation_zero k) (e k 44)
lemma arrow_span_326 (b : Fin 75) : a k b*normalRep k 326 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_326_60 k]
      exact normal_mem k 445
    · rw [extension_326_61 k]
      exact Submodule.zero_mem _
    · rw [extension_326_62 k]
      exact normal_mem k 444
  · rw [show a k b*normalRep k 326=0 from arrow_incompatible k b 44 40 [72, 37, 25] (normal_endpoints 326) h]
    exact Submodule.zero_mem _
lemma extension_327_14 : a k 14*normalRep k 327=normalRep k 443 := by
  change a k 14*walk k 44 [72, 38, 28]=walk k 44 [72, 37, 24, 18]
  rw [← walk_snoc]
  exact Universal.mul_reduced_155 (a k) (relation_zero k) (e k 44)
lemma arrow_span_327 (b : Fin 75) : a k b*normalRep k 327 ∈ normalSpan k := by
  by_cases h : arrowSource b=14
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [14] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_327_14 k]
      exact normal_mem k 443
  · rw [show a k b*normalRep k 327=0 from arrow_incompatible k b 44 14 [72, 38, 28] (normal_endpoints 327) h]
    exact Submodule.zero_mem _
lemma extension_328_60 : a k 60*normalRep k 328=0 := by
  change a k 60*walk k 44 [73, 67, 32]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_157 (a k) (relation_zero k) (e k 44)
lemma extension_328_61 : a k 61*normalRep k 328=normalRep k 446 := by
  exact (walk_snoc k 44 [73, 67, 32] 61).symm
lemma extension_328_62 : a k 62*normalRep k 328=normalRep k 447 := by
  exact (walk_snoc k 44 [73, 67, 32] 62).symm
lemma arrow_span_328 (b : Fin 75) : a k b*normalRep k 328 ∈ normalSpan k := by
  by_cases h : arrowSource b=40
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [60, 61, 62] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_328_60 k]
      exact Submodule.zero_mem _
    · rw [extension_328_61 k]
      exact normal_mem k 446
    · rw [extension_328_62 k]
      exact normal_mem k 447
  · rw [show a k b*normalRep k 328=0 from arrow_incompatible k b 44 40 [73, 67, 32] (normal_endpoints 328) h]
    exact Submodule.zero_mem _
lemma extension_329_12 : a k 12*normalRep k 329=normalRep k 446 := by
  change a k 12*walk k 44 [73, 68, 39]=walk k 44 [73, 67, 32, 61]
  rw [← walk_snoc]
  exact Universal.mul_reduced_165 (a k) (relation_zero k) (e k 44)
lemma arrow_span_329 (b : Fin 75) : a k b*normalRep k 329 ∈ normalSpan k := by
  by_cases h : arrowSource b=12
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [12] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_329_12 k]
      exact normal_mem k 446
  · rw [show a k b*normalRep k 329=0 from arrow_incompatible k b 44 12 [73, 68, 39] (normal_endpoints 329) h]
    exact Submodule.zero_mem _
lemma extension_330_26 : a k 26*normalRep k 330=normalRep k 448 := by
  exact (walk_snoc k 45 [74, 10, 11] 26).symm
lemma arrow_span_330 (b : Fin 75) : a k b*normalRep k 330 ∈ normalSpan k := by
  by_cases h : arrowSource b=21
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [26] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_330_26 k]
      exact normal_mem k 448
  · rw [show a k b*normalRep k 330=0 from arrow_incompatible k b 45 21 [74, 10, 11] (normal_endpoints 330) h]
    exact Submodule.zero_mem _
lemma extension_331_30 : a k 30*normalRep k 331=normalRep k 449 := by
  exact (walk_snoc k 1 [1, 34, 63, 20] 30).symm
lemma extension_331_31 : a k 31*normalRep k 331=0 := by
  change a k 31*walk k 1 [1, 34, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_240 (a k) (relation_zero k) (e k 1)
lemma arrow_span_331 (b : Fin 75) : a k b*normalRep k 331 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_331_30 k]
      exact normal_mem k 449
    · rw [extension_331_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 331=0 from arrow_incompatible k b 1 24 [1, 34, 63, 20] (normal_endpoints 331) h]
    exact Submodule.zero_mem _
lemma extension_332_54 : a k 54*normalRep k 332=normalRep k 450 := by
  exact (walk_snoc k 3 [3, 40, 60, 4] 54).symm
lemma extension_332_55 : a k 55*normalRep k 332=0 := by
  change a k 55*walk k 3 [3, 40, 60, 4]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_215 (a k) (relation_zero k) (e k 3)
lemma extension_332_56 : a k 56*normalRep k 332=normalRep k 451 := by
  exact (walk_snoc k 3 [3, 40, 60, 4] 56).symm
lemma arrow_span_332 (b : Fin 75) : a k b*normalRep k 332 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_332_54 k]
      exact normal_mem k 450
    · rw [extension_332_55 k]
      exact Submodule.zero_mem _
    · rw [extension_332_56 k]
      exact normal_mem k 451
  · rw [show a k b*normalRep k 332=0 from arrow_incompatible k b 3 38 [3, 40, 60, 4] (normal_endpoints 332) h]
    exact Submodule.zero_mem _
lemma extension_333_41 : a k 41*normalRep k 333=normalRep k 451 := by
  change a k 41*walk k 3 [3, 40, 62, 52]=walk k 3 [3, 40, 60, 4, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_278 (a k) (relation_zero k) (e k 3)
lemma extension_333_42 : a k 42*normalRep k 333=0 := by
  change a k 42*walk k 3 [3, 40, 62, 52]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_214 (a k) (relation_zero k) (e k 3)
lemma arrow_span_333 (b : Fin 75) : a k b*normalRep k 333 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_333_41 k]
      exact normal_mem k 451
    · rw [extension_333_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 333=0 from arrow_incompatible k b 3 31 [3, 40, 62, 52] (normal_endpoints 333) h]
    exact Submodule.zero_mem _
lemma extension_334_33 : a k 33*normalRep k 334=0 := by
  change a k 33*walk k 4 [4, 54, 15, 1]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_209 (a k) (relation_zero k) (e k 4)
lemma extension_334_34 : a k 34*normalRep k 334=normalRep k 452 := by
  exact (walk_snoc k 4 [4, 54, 15, 1] 34).symm
lemma arrow_span_334 (b : Fin 75) : a k b*normalRep k 334 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_334_33 k]
      exact Submodule.zero_mem _
    · rw [extension_334_34 k]
      exact normal_mem k 452
  · rw [show a k b*normalRep k 334=0 from arrow_incompatible k b 4 26 [4, 54, 15, 1] (normal_endpoints 334) h]
    exact Submodule.zero_mem _
lemma extension_335_5 : a k 5*normalRep k 335=normalRep k 452 := by
  change a k 5*walk k 4 [4, 54, 16, 57]=walk k 4 [4, 54, 15, 1, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_287 (a k) (relation_zero k) (e k 4)
lemma arrow_span_335 (b : Fin 75) : a k b*normalRep k 335 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_335_5 k]
      exact normal_mem k 452
  · rw [show a k b*normalRep k 335=0 from arrow_incompatible k b 4 5 [4, 54, 16, 57] (normal_endpoints 335) h]
    exact Submodule.zero_mem _
lemma extension_336_2 : a k 2*normalRep k 336=normalRep k 453 := by
  exact (walk_snoc k 5 [5, 63, 20, 30] 2).symm
lemma arrow_span_336 (b : Fin 75) : a k b*normalRep k 336 ∈ normalSpan k := by
  by_cases h : arrowSource b=2
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [2] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_336_2 k]
      exact normal_mem k 453
  · rw [show a k b*normalRep k 336=0 from arrow_incompatible k b 5 2 [5, 63, 20, 30] (normal_endpoints 336) h]
    exact Submodule.zero_mem _
lemma extension_337_69 : a k 69*normalRep k 337=normalRep k 454 := by
  exact (walk_snoc k 6 [6, 7, 17, 21] 69).symm
lemma extension_337_70 : a k 70*normalRep k 337=normalRep k 455 := by
  exact (walk_snoc k 6 [6, 7, 17, 21] 70).symm
lemma extension_337_71 : a k 71*normalRep k 337=0 := by
  change a k 71*walk k 6 [6, 7, 17, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_242 (a k) (relation_zero k) (e k 6)
lemma arrow_span_337 (b : Fin 75) : a k b*normalRep k 337 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_337_69 k]
      exact normal_mem k 454
    · rw [extension_337_70 k]
      exact normal_mem k 455
    · rw [extension_337_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 337=0 from arrow_incompatible k b 6 43 [6, 7, 17, 21] (normal_endpoints 337) h]
    exact Submodule.zero_mem _
lemma extension_338_8 : a k 8*normalRep k 338=normalRep k 456 := by
  exact (walk_snoc k 7 [7, 17, 21, 69] 8).symm
lemma arrow_span_338 (b : Fin 75) : a k b*normalRep k 338 ∈ normalSpan k := by
  by_cases h : arrowSource b=8
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [8] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_338_8 k]
      exact normal_mem k 456
  · rw [show a k b*normalRep k 338=0 from arrow_incompatible k b 7 8 [7, 17, 21, 69] (normal_endpoints 338) h]
    exact Submodule.zero_mem _
lemma extension_339_22 : a k 22*normalRep k 339=normalRep k 457 := by
  exact (walk_snoc k 7 [7, 17, 21, 70] 22).symm
lemma extension_339_23 : a k 23*normalRep k 339=(-normalRep k 456) := by
  change a k 23*walk k 7 [7, 17, 21, 70]=(-walk k 7 [7, 17, 21, 69, 8])
  rw [← walk_snoc]
  exact Universal.mul_reduced_305 (a k) (relation_zero k) (e k 7)
lemma arrow_span_339 (b : Fin 75) : a k b*normalRep k 339 ∈ normalSpan k := by
  by_cases h : arrowSource b=19
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [22, 23] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_339_22 k]
      exact normal_mem k 457
    · rw [extension_339_23 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 456)
  · rw [show a k b*normalRep k 339=0 from arrow_incompatible k b 7 19 [7, 17, 21, 70] (normal_endpoints 339) h]
    exact Submodule.zero_mem _
lemma extension_340_9 : a k 9*normalRep k 340=normalRep k 458 := by
  exact (walk_snoc k 8 [8, 66, 24, 18] 9).symm
lemma arrow_span_340 (b : Fin 75) : a k b*normalRep k 340 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_340_9 k]
      exact normal_mem k 458
  · rw [show a k b*normalRep k 340=0 from arrow_incompatible k b 8 9 [8, 66, 24, 18] (normal_endpoints 340) h]
    exact Submodule.zero_mem _
lemma extension_341_52 : a k 52*normalRep k 341=normalRep k 458 := by
  change a k 52*walk k 8 [8, 66, 24, 19]=walk k 8 [8, 66, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_237 (a k) (relation_zero k) (e k 8)
lemma extension_341_53 : a k 53*normalRep k 341=normalRep k 459 := by
  exact (walk_snoc k 8 [8, 66, 24, 19] 53).symm
lemma arrow_span_341 (b : Fin 75) : a k b*normalRep k 341 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_341_52 k]
      exact normal_mem k 458
    · rw [extension_341_53 k]
      exact normal_mem k 459
  · rw [show a k b*normalRep k 341=0 from arrow_incompatible k b 8 37 [8, 66, 24, 19] (normal_endpoints 341) h]
    exact Submodule.zero_mem _
lemma extension_342_4 : a k 4*normalRep k 342=normalRep k 459 := by
  change a k 4*walk k 8 [8, 66, 25, 60]=walk k 8 [8, 66, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_292 (a k) (relation_zero k) (e k 8)
lemma arrow_span_342 (b : Fin 75) : a k b*normalRep k 342 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_342_4 k]
      exact normal_mem k 459
  · rw [show a k b*normalRep k 342=0 from arrow_incompatible k b 8 4 [8, 66, 25, 60] (normal_endpoints 342) h]
    exact Submodule.zero_mem _
lemma extension_343_5 : a k 5*normalRep k 343=normalRep k 460 := by
  exact (walk_snoc k 9 [9, 41, 44, 57] 5).symm
lemma arrow_span_343 (b : Fin 75) : a k b*normalRep k 343 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_343_5 k]
      exact normal_mem k 460
  · rw [show a k b*normalRep k 343=0 from arrow_incompatible k b 9 5 [9, 41, 44, 57] (normal_endpoints 343) h]
    exact Submodule.zero_mem _
lemma extension_344_33 : a k 33*normalRep k 344=0 := by
  change a k 33*walk k 9 [9, 41, 44, 58]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_227 (a k) (relation_zero k) (e k 9)
lemma extension_344_34 : a k 34*normalRep k 344=normalRep k 460 := by
  change a k 34*walk k 9 [9, 41, 44, 58]=walk k 9 [9, 41, 44, 57, 5]
  rw [← walk_snoc]
  exact Universal.mul_reduced_288 (a k) (relation_zero k) (e k 9)
lemma arrow_span_344 (b : Fin 75) : a k b*normalRep k 344 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_344_33 k]
      exact Submodule.zero_mem _
    · rw [extension_344_34 k]
      exact normal_mem k 460
  · rw [show a k b*normalRep k 344=0 from arrow_incompatible k b 9 26 [9, 41, 44, 58] (normal_endpoints 344) h]
    exact Submodule.zero_mem _
lemma extension_345_72 : a k 72*normalRep k 345=0 := by
  change a k 72*walk k 10 [10, 11, 26, 31]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_255 (a k) (relation_zero k) (e k 10)
lemma extension_345_73 : a k 73*normalRep k 345=normalRep k 461 := by
  exact (walk_snoc k 10 [10, 11, 26, 31] 73).symm
lemma arrow_span_345 (b : Fin 75) : a k b*normalRep k 345 ∈ normalSpan k := by
  by_cases h : arrowSource b=44
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [72, 73] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_345_72 k]
      exact Submodule.zero_mem _
    · rw [extension_345_73 k]
      exact normal_mem k 461
  · rw [show a k b*normalRep k 345=0 from arrow_incompatible k b 10 44 [10, 11, 26, 31] (normal_endpoints 345) h]
    exact Submodule.zero_mem _
lemma extension_346_66 : a k 66*normalRep k 346=0 := by
  change a k 66*walk k 11 [11, 26, 31, 73]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_310 (a k) (relation_zero k) (e k 11)
lemma extension_346_67 : a k 67*normalRep k 346=normalRep k 462 := by
  exact (walk_snoc k 11 [11, 26, 31, 73] 67).symm
lemma extension_346_68 : a k 68*normalRep k 346=normalRep k 463 := by
  exact (walk_snoc k 11 [11, 26, 31, 73] 68).symm
lemma arrow_span_346 (b : Fin 75) : a k b*normalRep k 346 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_346_66 k]
      exact Submodule.zero_mem _
    · rw [extension_346_67 k]
      exact normal_mem k 462
    · rw [extension_346_68 k]
      exact normal_mem k 463
  · rw [show a k b*normalRep k 346=0 from arrow_incompatible k b 11 42 [11, 26, 31, 73] (normal_endpoints 346) h]
    exact Submodule.zero_mem _
lemma extension_347_57 : a k 57*normalRep k 347=0 := by
  change a k 57*walk k 12 [12, 35, 55, 27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_252 (a k) (relation_zero k) (e k 12)
lemma extension_347_58 : a k 58*normalRep k 347=normalRep k 464 := by
  exact (walk_snoc k 12 [12, 35, 55, 27] 58).symm
lemma extension_347_59 : a k 59*normalRep k 347=normalRep k 465 := by
  exact (walk_snoc k 12 [12, 35, 55, 27] 59).symm
lemma arrow_span_347 (b : Fin 75) : a k b*normalRep k 347 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_347_57 k]
      exact Submodule.zero_mem _
    · rw [extension_347_58 k]
      exact normal_mem k 464
    · rw [extension_347_59 k]
      exact normal_mem k 465
  · rw [show a k b*normalRep k 347=0 from arrow_incompatible k b 12 39 [12, 35, 55, 27] (normal_endpoints 347) h]
    exact Submodule.zero_mem _
lemma extension_348_47 : a k 47*normalRep k 348=normalRep k 466 := by
  exact (walk_snoc k 12 [12, 35, 56, 43] 47).symm
lemma extension_348_48 : a k 48*normalRep k 348=normalRep k 465 := by
  change a k 48*walk k 12 [12, 35, 56, 43]=walk k 12 [12, 35, 55, 27, 59]
  rw [← walk_snoc]
  exact Universal.mul_reduced_268 (a k) (relation_zero k) (e k 12)
lemma arrow_span_348 (b : Fin 75) : a k b*normalRep k 348 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_348_47 k]
      exact normal_mem k 466
    · rw [extension_348_48 k]
      exact normal_mem k 465
  · rw [show a k b*normalRep k 348=0 from arrow_incompatible k b 12 34 [12, 35, 56, 43] (normal_endpoints 348) h]
    exact Submodule.zero_mem _
lemma extension_349_66 : a k 66*normalRep k 349=normalRep k 467 := by
  exact (walk_snoc k 13 [13, 49, 69, 8] 66).symm
lemma extension_349_67 : a k 67*normalRep k 349=0 := by
  change a k 67*walk k 13 [13, 49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_224 (a k) (relation_zero k) (e k 13)
lemma extension_349_68 : a k 68*normalRep k 349=normalRep k 468 := by
  exact (walk_snoc k 13 [13, 49, 69, 8] 68).symm
lemma arrow_span_349 (b : Fin 75) : a k b*normalRep k 349 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_349_66 k]
      exact normal_mem k 467
    · rw [extension_349_67 k]
      exact Submodule.zero_mem _
    · rw [extension_349_68 k]
      exact normal_mem k 468
  · rw [show a k b*normalRep k 349=0 from arrow_incompatible k b 13 42 [13, 49, 69, 8] (normal_endpoints 349) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
