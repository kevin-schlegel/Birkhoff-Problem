import N6NormalData
import N6Reduced1
import N6Reduced2
import N6Reduced3
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma extension_250_66 : a k 66*normalRep k 250=0 := by
  change a k 66*walk k 21 [26, 31, 73]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_206 (a k) (relation_zero k) (e k 21)
lemma extension_250_67 : a k 67*normalRep k 250=normalRep k 365 := by
  exact (walk_snoc k 21 [26, 31, 73] 67).symm
lemma extension_250_68 : a k 68*normalRep k 250=normalRep k 366 := by
  exact (walk_snoc k 21 [26, 31, 73] 68).symm
lemma arrow_span_250 (b : Fin 75) : a k b*normalRep k 250 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_250_66 k]
      exact Submodule.zero_mem _
    · rw [extension_250_67 k]
      exact normal_mem k 365
    · rw [extension_250_68 k]
      exact normal_mem k 366
  · rw [show a k b*normalRep k 250=0 from arrow_incompatible k b 21 42 [26, 31, 73] (normal_endpoints 250) h]
    exact Submodule.zero_mem _
lemma extension_251_13 : a k 13*normalRep k 251=normalRep k 367 := by
  exact (walk_snoc k 22 [27, 58, 33] 13).symm
lemma arrow_span_251 (b : Fin 75) : a k b*normalRep k 251 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_251_13 k]
      exact normal_mem k 367
  · rw [show a k b*normalRep k 251=0 from arrow_incompatible k b 22 13 [27, 58, 33] (normal_endpoints 251) h]
    exact Submodule.zero_mem _
lemma extension_252_63 : a k 63*normalRep k 252=normalRep k 368 := by
  exact (walk_snoc k 22 [27, 58, 34] 63).symm
lemma extension_252_64 : a k 64*normalRep k 252=normalRep k 369 := by
  exact (walk_snoc k 22 [27, 58, 34] 64).symm
lemma extension_252_65 : a k 65*normalRep k 252=normalRep k 367 := by
  change a k 65*walk k 22 [27, 58, 34]=walk k 22 [27, 58, 33, 13]
  rw [← walk_snoc]
  exact Universal.mul_reduced_158 (a k) (relation_zero k) (e k 22)
lemma arrow_span_252 (b : Fin 75) : a k b*normalRep k 252 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_252_63 k]
      exact normal_mem k 368
    · rw [extension_252_64 k]
      exact normal_mem k 369
    · rw [extension_252_65 k]
      exact normal_mem k 367
  · rw [show a k b*normalRep k 252=0 from arrow_incompatible k b 22 41 [27, 58, 34] (normal_endpoints 252) h]
    exact Submodule.zero_mem _
lemma extension_253_17 : a k 17*normalRep k 253=normalRep k 368 := by
  change a k 17*walk k 22 [27, 59, 50]=walk k 22 [27, 58, 34, 63]
  rw [← walk_snoc]
  exact Universal.mul_reduced_177 (a k) (relation_zero k) (e k 22)
lemma arrow_span_253 (b : Fin 75) : a k b*normalRep k 253 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_253_17 k]
      exact normal_mem k 368
  · rw [show a k b*normalRep k 253=0 from arrow_incompatible k b 22 16 [27, 59, 50] (normal_endpoints 253) h]
    exact Submodule.zero_mem _
lemma extension_254_41 : a k 41*normalRep k 254=normalRep k 370 := by
  exact (walk_snoc k 23 [28, 14, 9] 41).symm
lemma extension_254_42 : a k 42*normalRep k 254=0 := by
  change a k 42*walk k 23 [28, 14, 9]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_127 (a k) (relation_zero k) (e k 23)
lemma arrow_span_254 (b : Fin 75) : a k b*normalRep k 254 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_254_41 k]
      exact normal_mem k 370
    · rw [extension_254_42 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 254=0 from arrow_incompatible k b 23 31 [28, 14, 9] (normal_endpoints 254) h]
    exact Submodule.zero_mem _
lemma extension_255_54 : a k 54*normalRep k 255=normalRep k 371 := by
  exact (walk_snoc k 23 [29, 19, 53] 54).symm
lemma extension_255_55 : a k 55*normalRep k 255=0 := by
  change a k 55*walk k 23 [29, 19, 53]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_135 (a k) (relation_zero k) (e k 23)
lemma extension_255_56 : a k 56*normalRep k 255=normalRep k 370 := by
  change a k 56*walk k 23 [29, 19, 53]=walk k 23 [28, 14, 9, 41]
  rw [← walk_snoc]
  exact Universal.mul_reduced_181 (a k) (relation_zero k) (e k 23)
lemma arrow_span_255 (b : Fin 75) : a k b*normalRep k 255 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_255_54 k]
      exact normal_mem k 371
    · rw [extension_255_55 k]
      exact Submodule.zero_mem _
    · rw [extension_255_56 k]
      exact normal_mem k 370
  · rw [show a k b*normalRep k 255=0 from arrow_incompatible k b 23 38 [29, 19, 53] (normal_endpoints 255) h]
    exact Submodule.zero_mem _
lemma arrow_span_256 (b : Fin 75) : a k b*normalRep k 256 ∈ normalSpan k := by
  by_cases h : arrowSource b=46
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
  · rw [show a k b*normalRep k 256=0 from arrow_incompatible k b 24 46 [30, 2, 0] (normal_endpoints 256) h]
    exact Submodule.zero_mem _
lemma extension_257_32 : a k 32*normalRep k 257=normalRep k 372 := by
  exact (walk_snoc k 24 [31, 73, 67] 32).symm
lemma arrow_span_257 (b : Fin 75) : a k b*normalRep k 257 ∈ normalSpan k := by
  by_cases h : arrowSource b=25
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [32] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_257_32 k]
      exact normal_mem k 372
  · rw [show a k b*normalRep k 257=0 from arrow_incompatible k b 24 25 [31, 73, 67] (normal_endpoints 257) h]
    exact Submodule.zero_mem _
lemma extension_258_39 : a k 39*normalRep k 258=normalRep k 373 := by
  exact (walk_snoc k 24 [31, 73, 68] 39).symm
lemma extension_258_40 : a k 40*normalRep k 258=normalRep k 372 := by
  change a k 40*walk k 24 [31, 73, 68]=walk k 24 [31, 73, 67, 32]
  rw [← walk_snoc]
  exact Universal.mul_reduced_199 (a k) (relation_zero k) (e k 24)
lemma arrow_span_258 (b : Fin 75) : a k b*normalRep k 258 ∈ normalSpan k := by
  by_cases h : arrowSource b=30
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [39, 40] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_258_39 k]
      exact normal_mem k 373
    · rw [extension_258_40 k]
      exact normal_mem k 372
  · rw [show a k b*normalRep k 258=0 from arrow_incompatible k b 24 30 [31, 73, 68] (normal_endpoints 258) h]
    exact Submodule.zero_mem _
lemma extension_259_54 : a k 54*normalRep k 259=0 := by
  change a k 54*walk k 25 [32, 61, 35]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_160 (a k) (relation_zero k) (e k 25)
lemma extension_259_55 : a k 55*normalRep k 259=normalRep k 374 := by
  exact (walk_snoc k 25 [32, 61, 35] 55).symm
lemma extension_259_56 : a k 56*normalRep k 259=normalRep k 375 := by
  exact (walk_snoc k 25 [32, 61, 35] 56).symm
lemma arrow_span_259 (b : Fin 75) : a k b*normalRep k 259 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_259_54 k]
      exact Submodule.zero_mem _
    · rw [extension_259_55 k]
      exact normal_mem k 374
    · rw [extension_259_56 k]
      exact normal_mem k 375
  · rw [show a k b*normalRep k 259=0 from arrow_incompatible k b 25 38 [32, 61, 35] (normal_endpoints 259) h]
    exact Submodule.zero_mem _
lemma extension_260_41 : a k 41*normalRep k 260=normalRep k 375 := by
  change a k 41*walk k 25 [32, 62, 52]=walk k 25 [32, 61, 35, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_182 (a k) (relation_zero k) (e k 25)
lemma extension_260_42 : a k 42*normalRep k 260=normalRep k 376 := by
  exact (walk_snoc k 25 [32, 62, 52] 42).symm
lemma arrow_span_260 (b : Fin 75) : a k b*normalRep k 260 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_260_41 k]
      exact normal_mem k 375
    · rw [extension_260_42 k]
      exact normal_mem k 376
  · rw [show a k b*normalRep k 260=0 from arrow_incompatible k b 25 31 [32, 62, 52] (normal_endpoints 260) h]
    exact Submodule.zero_mem _
lemma extension_261_69 : a k 69*normalRep k 261=normalRep k 377 := by
  exact (walk_snoc k 26 [33, 13, 49] 69).symm
lemma extension_261_70 : a k 70*normalRep k 261=0 := by
  change a k 70*walk k 26 [33, 13, 49]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_175 (a k) (relation_zero k) (e k 26)
lemma extension_261_71 : a k 71*normalRep k 261=normalRep k 378 := by
  exact (walk_snoc k 26 [33, 13, 49] 71).symm
lemma arrow_span_261 (b : Fin 75) : a k b*normalRep k 261 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_261_69 k]
      exact normal_mem k 377
    · rw [extension_261_70 k]
      exact Submodule.zero_mem _
    · rw [extension_261_71 k]
      exact normal_mem k 378
  · rw [show a k b*normalRep k 261=0 from arrow_incompatible k b 26 43 [33, 13, 49] (normal_endpoints 261) h]
    exact Submodule.zero_mem _
lemma extension_262_30 : a k 30*normalRep k 262=normalRep k 379 := by
  exact (walk_snoc k 26 [34, 63, 20] 30).symm
lemma extension_262_31 : a k 31*normalRep k 262=0 := by
  change a k 31*walk k 26 [34, 63, 20]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_139 (a k) (relation_zero k) (e k 26)
lemma arrow_span_262 (b : Fin 75) : a k b*normalRep k 262 ∈ normalSpan k := by
  by_cases h : arrowSource b=24
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [30, 31] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_262_30 k]
      exact normal_mem k 379
    · rw [extension_262_31 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 262=0 from arrow_incompatible k b 26 24 [34, 63, 20] (normal_endpoints 262) h]
    exact Submodule.zero_mem _
lemma extension_263_69 : a k 69*normalRep k 263=(-normalRep k 377) := by
  change a k 69*walk k 26 [34, 63, 21]=(-walk k 26 [33, 13, 49, 69])
  rw [← walk_snoc]
  exact Universal.mul_reduced_162 (a k) (relation_zero k) (e k 26)
lemma extension_263_70 : a k 70*normalRep k 263=normalRep k 380 := by
  exact (walk_snoc k 26 [34, 63, 21] 70).symm
lemma extension_263_71 : a k 71*normalRep k 263=0 := by
  change a k 71*walk k 26 [34, 63, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_141 (a k) (relation_zero k) (e k 26)
lemma arrow_span_263 (b : Fin 75) : a k b*normalRep k 263 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_263_69 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 377)
    · rw [extension_263_70 k]
      exact normal_mem k 380
    · rw [extension_263_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 263=0 from arrow_incompatible k b 26 43 [34, 63, 21] (normal_endpoints 263) h]
    exact Submodule.zero_mem _
lemma extension_264_57 : a k 57*normalRep k 264=0 := by
  change a k 57*walk k 27 [35, 55, 27]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_153 (a k) (relation_zero k) (e k 27)
lemma extension_264_58 : a k 58*normalRep k 264=normalRep k 381 := by
  exact (walk_snoc k 27 [35, 55, 27] 58).symm
lemma extension_264_59 : a k 59*normalRep k 264=normalRep k 382 := by
  exact (walk_snoc k 27 [35, 55, 27] 59).symm
lemma arrow_span_264 (b : Fin 75) : a k b*normalRep k 264 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_264_57 k]
      exact Submodule.zero_mem _
    · rw [extension_264_58 k]
      exact normal_mem k 381
    · rw [extension_264_59 k]
      exact normal_mem k 382
  · rw [show a k b*normalRep k 264=0 from arrow_incompatible k b 27 39 [35, 55, 27] (normal_endpoints 264) h]
    exact Submodule.zero_mem _
lemma extension_265_47 : a k 47*normalRep k 265=normalRep k 383 := by
  exact (walk_snoc k 27 [35, 56, 43] 47).symm
lemma extension_265_48 : a k 48*normalRep k 265=normalRep k 382 := by
  change a k 48*walk k 27 [35, 56, 43]=walk k 27 [35, 55, 27, 59]
  rw [← walk_snoc]
  exact Universal.mul_reduced_170 (a k) (relation_zero k) (e k 27)
lemma arrow_span_265 (b : Fin 75) : a k b*normalRep k 265 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_265_47 k]
      exact normal_mem k 383
    · rw [extension_265_48 k]
      exact normal_mem k 382
  · rw [show a k b*normalRep k 265=0 from arrow_incompatible k b 27 34 [35, 56, 43] (normal_endpoints 265) h]
    exact Submodule.zero_mem _
lemma extension_266_3 : a k 3*normalRep k 266=normalRep k 384 := by
  exact (walk_snoc k 28 [36, 70, 22] 3).symm
lemma arrow_span_266 (b : Fin 75) : a k b*normalRep k 266 ∈ normalSpan k := by
  by_cases h : arrowSource b=3
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [3] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_266_3 k]
      exact normal_mem k 384
  · rw [show a k b*normalRep k 266=0 from arrow_incompatible k b 28 3 [36, 70, 22] (normal_endpoints 266) h]
    exact Submodule.zero_mem _
lemma extension_267_66 : a k 66*normalRep k 267=normalRep k 385 := by
  exact (walk_snoc k 28 [36, 70, 23] 66).symm
lemma extension_267_67 : a k 67*normalRep k 267=0 := by
  change a k 67*walk k 28 [36, 70, 23]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_143 (a k) (relation_zero k) (e k 28)
lemma extension_267_68 : a k 68*normalRep k 267=(-normalRep k 384) := by
  change a k 68*walk k 28 [36, 70, 23]=(-walk k 28 [36, 70, 22, 3])
  rw [← walk_snoc]
  exact Universal.mul_reduced_145 (a k) (relation_zero k) (e k 28)
lemma arrow_span_267 (b : Fin 75) : a k b*normalRep k 267 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_267_66 k]
      exact normal_mem k 385
    · rw [extension_267_67 k]
      exact Submodule.zero_mem _
    · rw [extension_267_68 k]
      exact (normalSpan k).smul_mem (-1:k) (normal_mem k 384)
  · rw [show a k b*normalRep k 267=0 from arrow_incompatible k b 28 42 [36, 70, 23] (normal_endpoints 267) h]
    exact Submodule.zero_mem _
lemma extension_268_37 : a k 37*normalRep k 268=normalRep k 385 := by
  change a k 37*walk k 28 [36, 71, 72]=walk k 28 [36, 70, 23, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_207 (a k) (relation_zero k) (e k 28)
lemma extension_268_38 : a k 38*normalRep k 268=normalRep k 386 := by
  exact (walk_snoc k 28 [36, 71, 72] 38).symm
lemma arrow_span_268 (b : Fin 75) : a k b*normalRep k 268 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_268_37 k]
      exact normal_mem k 385
    · rw [extension_268_38 k]
      exact normal_mem k 386
  · rw [show a k b*normalRep k 268=0 from arrow_incompatible k b 28 29 [36, 71, 72] (normal_endpoints 268) h]
    exact Submodule.zero_mem _
lemma extension_269_9 : a k 9*normalRep k 269=normalRep k 387 := by
  exact (walk_snoc k 29 [37, 24, 18] 9).symm
lemma arrow_span_269 (b : Fin 75) : a k b*normalRep k 269 ∈ normalSpan k := by
  by_cases h : arrowSource b=9
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [9] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_269_9 k]
      exact normal_mem k 387
  · rw [show a k b*normalRep k 269=0 from arrow_incompatible k b 29 9 [37, 24, 18] (normal_endpoints 269) h]
    exact Submodule.zero_mem _
lemma extension_270_52 : a k 52*normalRep k 270=normalRep k 387 := by
  change a k 52*walk k 29 [37, 24, 19]=walk k 29 [37, 24, 18, 9]
  rw [← walk_snoc]
  exact Universal.mul_reduced_136 (a k) (relation_zero k) (e k 29)
lemma extension_270_53 : a k 53*normalRep k 270=normalRep k 388 := by
  exact (walk_snoc k 29 [37, 24, 19] 53).symm
lemma arrow_span_270 (b : Fin 75) : a k b*normalRep k 270 ∈ normalSpan k := by
  by_cases h : arrowSource b=37
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [52, 53] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_270_52 k]
      exact normal_mem k 387
    · rw [extension_270_53 k]
      exact normal_mem k 388
  · rw [show a k b*normalRep k 270=0 from arrow_incompatible k b 29 37 [37, 24, 19] (normal_endpoints 270) h]
    exact Submodule.zero_mem _
lemma extension_271_4 : a k 4*normalRep k 271=normalRep k 388 := by
  change a k 4*walk k 29 [37, 25, 60]=walk k 29 [37, 24, 19, 53]
  rw [← walk_snoc]
  exact Universal.mul_reduced_192 (a k) (relation_zero k) (e k 29)
lemma arrow_span_271 (b : Fin 75) : a k b*normalRep k 271 ∈ normalSpan k := by
  by_cases h : arrowSource b=4
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [4] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_271_4 k]
      exact normal_mem k 388
  · rw [show a k b*normalRep k 271=0 from arrow_incompatible k b 29 4 [37, 25, 60] (normal_endpoints 271) h]
    exact Submodule.zero_mem _
lemma extension_272_54 : a k 54*normalRep k 272=0 := by
  change a k 54*walk k 30 [39, 12, 35]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_161 (a k) (relation_zero k) (e k 30)
lemma extension_272_55 : a k 55*normalRep k 272=normalRep k 389 := by
  exact (walk_snoc k 30 [39, 12, 35] 55).symm
lemma extension_272_56 : a k 56*normalRep k 272=normalRep k 390 := by
  exact (walk_snoc k 30 [39, 12, 35] 56).symm
lemma arrow_span_272 (b : Fin 75) : a k b*normalRep k 272 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_272_54 k]
      exact Submodule.zero_mem _
    · rw [extension_272_55 k]
      exact normal_mem k 389
    · rw [extension_272_56 k]
      exact normal_mem k 390
  · rw [show a k b*normalRep k 272=0 from arrow_incompatible k b 30 38 [39, 12, 35] (normal_endpoints 272) h]
    exact Submodule.zero_mem _
lemma extension_273_54 : a k 54*normalRep k 273=normalRep k 391 := by
  exact (walk_snoc k 30 [40, 60, 4] 54).symm
lemma extension_273_55 : a k 55*normalRep k 273=0 := by
  change a k 55*walk k 30 [40, 60, 4]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_118 (a k) (relation_zero k) (e k 30)
lemma extension_273_56 : a k 56*normalRep k 273=normalRep k 392 := by
  exact (walk_snoc k 30 [40, 60, 4] 56).symm
lemma arrow_span_273 (b : Fin 75) : a k b*normalRep k 273 ∈ normalSpan k := by
  by_cases h : arrowSource b=38
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [54, 55, 56] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_273_54 k]
      exact normal_mem k 391
    · rw [extension_273_55 k]
      exact Submodule.zero_mem _
    · rw [extension_273_56 k]
      exact normal_mem k 392
  · rw [show a k b*normalRep k 273=0 from arrow_incompatible k b 30 38 [40, 60, 4] (normal_endpoints 273) h]
    exact Submodule.zero_mem _
lemma extension_274_41 : a k 41*normalRep k 274=normalRep k 392 + normalRep k 390 := by
  change a k 41*walk k 30 [40, 62, 52]=walk k 30 [40, 60, 4, 56] + walk k 30 [39, 12, 35, 56]
  rw [← walk_snoc]
  exact Universal.mul_reduced_183 (a k) (relation_zero k) (e k 30)
lemma extension_274_42 : a k 42*normalRep k 274=normalRep k 393 := by
  exact (walk_snoc k 30 [40, 62, 52] 42).symm
lemma arrow_span_274 (b : Fin 75) : a k b*normalRep k 274 ∈ normalSpan k := by
  by_cases h : arrowSource b=31
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [41, 42] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_274_41 k]
      exact (normalSpan k).add_mem (normal_mem k 392) (normal_mem k 390)
    · rw [extension_274_42 k]
      exact normal_mem k 393
  · rw [show a k b*normalRep k 274=0 from arrow_incompatible k b 30 31 [40, 62, 52] (normal_endpoints 274) h]
    exact Submodule.zero_mem _
lemma extension_275_7 : a k 7*normalRep k 275=normalRep k 394 := by
  exact (walk_snoc k 31 [41, 43, 47] 7).symm
lemma arrow_span_275 (b : Fin 75) : a k b*normalRep k 275 ∈ normalSpan k := by
  by_cases h : arrowSource b=7
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [7] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_275_7 k]
      exact normal_mem k 394
  · rw [show a k b*normalRep k 275=0 from arrow_incompatible k b 31 7 [41, 43, 47] (normal_endpoints 275) h]
    exact Submodule.zero_mem _
lemma extension_276_50 : a k 50*normalRep k 276=normalRep k 394 := by
  change a k 50*walk k 31 [41, 43, 48]=walk k 31 [41, 43, 47, 7]
  rw [← walk_snoc]
  exact Universal.mul_reduced_173 (a k) (relation_zero k) (e k 31)
lemma extension_276_51 : a k 51*normalRep k 276=normalRep k 395 := by
  exact (walk_snoc k 31 [41, 43, 48] 51).symm
lemma arrow_span_276 (b : Fin 75) : a k b*normalRep k 276 ∈ normalSpan k := by
  by_cases h : arrowSource b=36
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [50, 51] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_276_50 k]
      exact normal_mem k 394
    · rw [extension_276_51 k]
      exact normal_mem k 395
  · rw [show a k b*normalRep k 276=0 from arrow_incompatible k b 31 36 [41, 43, 48] (normal_endpoints 276) h]
    exact Submodule.zero_mem _
lemma extension_277_5 : a k 5*normalRep k 277=normalRep k 396 := by
  exact (walk_snoc k 31 [41, 44, 57] 5).symm
lemma arrow_span_277 (b : Fin 75) : a k b*normalRep k 277 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_277_5 k]
      exact normal_mem k 396
  · rw [show a k b*normalRep k 277=0 from arrow_incompatible k b 31 5 [41, 44, 57] (normal_endpoints 277) h]
    exact Submodule.zero_mem _
lemma extension_278_33 : a k 33*normalRep k 278=normalRep k 397 := by
  exact (walk_snoc k 31 [41, 44, 58] 33).symm
lemma extension_278_34 : a k 34*normalRep k 278=normalRep k 396 + normalRep k 395 := by
  change a k 34*walk k 31 [41, 44, 58]=walk k 31 [41, 44, 57, 5] + walk k 31 [41, 43, 48, 51]
  rw [← walk_snoc]
  exact Universal.mul_reduced_188 (a k) (relation_zero k) (e k 31)
lemma arrow_span_278 (b : Fin 75) : a k b*normalRep k 278 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_278_33 k]
      exact normal_mem k 397
    · rw [extension_278_34 k]
      exact (normalSpan k).add_mem (normal_mem k 396) (normal_mem k 395)
  · rw [show a k b*normalRep k 278=0 from arrow_incompatible k b 31 26 [41, 44, 58] (normal_endpoints 278) h]
    exact Submodule.zero_mem _
lemma extension_279_17 : a k 17*normalRep k 279=normalRep k 398 := by
  exact (walk_snoc k 32 [43, 47, 7] 17).symm
lemma arrow_span_279 (b : Fin 75) : a k b*normalRep k 279 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_279_17 k]
      exact normal_mem k 398
  · rw [show a k b*normalRep k 279=0 from arrow_incompatible k b 32 16 [43, 47, 7] (normal_endpoints 279) h]
    exact Submodule.zero_mem _
lemma extension_280_63 : a k 63*normalRep k 280=normalRep k 398 := by
  change a k 63*walk k 32 [43, 48, 51]=walk k 32 [43, 47, 7, 17]
  rw [← walk_snoc]
  exact Universal.mul_reduced_178 (a k) (relation_zero k) (e k 32)
lemma extension_280_64 : a k 64*normalRep k 280=normalRep k 399 := by
  exact (walk_snoc k 32 [43, 48, 51] 64).symm
lemma extension_280_65 : a k 65*normalRep k 280=normalRep k 400 := by
  exact (walk_snoc k 32 [43, 48, 51] 65).symm
lemma arrow_span_280 (b : Fin 75) : a k b*normalRep k 280 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_280_63 k]
      exact normal_mem k 398
    · rw [extension_280_64 k]
      exact normal_mem k 399
    · rw [extension_280_65 k]
      exact normal_mem k 400
  · rw [show a k b*normalRep k 280=0 from arrow_incompatible k b 32 41 [43, 48, 51] (normal_endpoints 280) h]
    exact Submodule.zero_mem _
lemma extension_281_63 : a k 63*normalRep k 281=normalRep k 401 := by
  exact (walk_snoc k 32 [44, 57, 5] 63).symm
lemma extension_281_64 : a k 64*normalRep k 281=0 := by
  change a k 64*walk k 32 [44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_120 (a k) (relation_zero k) (e k 32)
lemma extension_281_65 : a k 65*normalRep k 281=0 := by
  change a k 65*walk k 32 [44, 57, 5]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_122 (a k) (relation_zero k) (e k 32)
lemma arrow_span_281 (b : Fin 75) : a k b*normalRep k 281 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_281_63 k]
      exact normal_mem k 401
    · rw [extension_281_64 k]
      exact Submodule.zero_mem _
    · rw [extension_281_65 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 281=0 from arrow_incompatible k b 32 41 [44, 57, 5] (normal_endpoints 281) h]
    exact Submodule.zero_mem _
lemma extension_282_13 : a k 13*normalRep k 282=normalRep k 400 := by
  change a k 13*walk k 32 [44, 58, 33]=walk k 32 [43, 48, 51, 65]
  rw [← walk_snoc]
  exact Universal.mul_reduced_159 (a k) (relation_zero k) (e k 32)
lemma arrow_span_282 (b : Fin 75) : a k b*normalRep k 282 ∈ normalSpan k := by
  by_cases h : arrowSource b=13
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [13] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_282_13 k]
      exact normal_mem k 400
  · rw [show a k b*normalRep k 282=0 from arrow_incompatible k b 32 13 [44, 58, 33] (normal_endpoints 282) h]
    exact Submodule.zero_mem _
lemma extension_283_17 : a k 17*normalRep k 283=normalRep k 402 := by
  exact (walk_snoc k 33 [45, 6, 7] 17).symm
lemma arrow_span_283 (b : Fin 75) : a k b*normalRep k 283 ∈ normalSpan k := by
  by_cases h : arrowSource b=16
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [17] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_283_17 k]
      exact normal_mem k 402
  · rw [show a k b*normalRep k 283=0 from arrow_incompatible k b 33 16 [45, 6, 7] (normal_endpoints 283) h]
    exact Submodule.zero_mem _
lemma extension_284_63 : a k 63*normalRep k 284=normalRep k 402 := by
  change a k 63*walk k 33 [46, 48, 51]=walk k 33 [45, 6, 7, 17]
  rw [← walk_snoc]
  exact Universal.mul_reduced_179 (a k) (relation_zero k) (e k 33)
lemma extension_284_64 : a k 64*normalRep k 284=normalRep k 403 := by
  exact (walk_snoc k 33 [46, 48, 51] 64).symm
lemma extension_284_65 : a k 65*normalRep k 284=normalRep k 404 := by
  exact (walk_snoc k 33 [46, 48, 51] 65).symm
lemma arrow_span_284 (b : Fin 75) : a k b*normalRep k 284 ∈ normalSpan k := by
  by_cases h : arrowSource b=41
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [63, 64, 65] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_284_63 k]
      exact normal_mem k 402
    · rw [extension_284_64 k]
      exact normal_mem k 403
    · rw [extension_284_65 k]
      exact normal_mem k 404
  · rw [show a k b*normalRep k 284=0 from arrow_incompatible k b 33 41 [46, 48, 51] (normal_endpoints 284) h]
    exact Submodule.zero_mem _
lemma extension_285_20 : a k 20*normalRep k 285=0 := by
  change a k 20*walk k 34 [47, 7, 17]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_133 (a k) (relation_zero k) (e k 34)
lemma extension_285_21 : a k 21*normalRep k 285=normalRep k 405 := by
  exact (walk_snoc k 34 [47, 7, 17] 21).symm
lemma arrow_span_285 (b : Fin 75) : a k b*normalRep k 285 ∈ normalSpan k := by
  by_cases h : arrowSource b=18
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [20, 21] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_285_20 k]
      exact Submodule.zero_mem _
    · rw [extension_285_21 k]
      exact normal_mem k 405
  · rw [show a k b*normalRep k 285=0 from arrow_incompatible k b 34 18 [47, 7, 17] (normal_endpoints 285) h]
    exact Submodule.zero_mem _
lemma extension_286_36 : a k 36*normalRep k 286=normalRep k 406 := by
  exact (walk_snoc k 34 [48, 51, 64] 36).symm
lemma arrow_span_286 (b : Fin 75) : a k b*normalRep k 286 ∈ normalSpan k := by
  by_cases h : arrowSource b=28
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [36] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_286_36 k]
      exact normal_mem k 406
  · rw [show a k b*normalRep k 286=0 from arrow_incompatible k b 34 28 [48, 51, 64] (normal_endpoints 286) h]
    exact Submodule.zero_mem _
lemma extension_287_49 : a k 49*normalRep k 287=(-normalRep k 405) + normalRep k 406 := by
  change a k 49*walk k 34 [48, 51, 65]=(-walk k 34 [47, 7, 17, 21]) + walk k 34 [48, 51, 64, 36]
  rw [← walk_snoc]
  exact Universal.mul_reduced_196 (a k) (relation_zero k) (e k 34)
lemma arrow_span_287 (b : Fin 75) : a k b*normalRep k 287 ∈ normalSpan k := by
  by_cases h : arrowSource b=35
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [49] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_287_49 k]
      exact (normalSpan k).add_mem ((normalSpan k).smul_mem (-1:k) (normal_mem k 405)) (normal_mem k 406)
  · rw [show a k b*normalRep k 287=0 from arrow_incompatible k b 34 35 [48, 51, 65] (normal_endpoints 287) h]
    exact Submodule.zero_mem _
lemma extension_288_66 : a k 66*normalRep k 288=normalRep k 407 := by
  exact (walk_snoc k 35 [49, 69, 8] 66).symm
lemma extension_288_67 : a k 67*normalRep k 288=0 := by
  change a k 67*walk k 35 [49, 69, 8]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_125 (a k) (relation_zero k) (e k 35)
lemma extension_288_68 : a k 68*normalRep k 288=normalRep k 408 := by
  exact (walk_snoc k 35 [49, 69, 8] 68).symm
lemma arrow_span_288 (b : Fin 75) : a k b*normalRep k 288 ∈ normalSpan k := by
  by_cases h : arrowSource b=42
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [66, 67, 68] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_288_66 k]
      exact normal_mem k 407
    · rw [extension_288_67 k]
      exact Submodule.zero_mem _
    · rw [extension_288_68 k]
      exact normal_mem k 408
  · rw [show a k b*normalRep k 288=0 from arrow_incompatible k b 35 42 [49, 69, 8] (normal_endpoints 288) h]
    exact Submodule.zero_mem _
lemma extension_289_37 : a k 37*normalRep k 289=normalRep k 407 := by
  change a k 37*walk k 35 [49, 71, 72]=walk k 35 [49, 69, 8, 66]
  rw [← walk_snoc]
  exact Universal.mul_reduced_208 (a k) (relation_zero k) (e k 35)
lemma extension_289_38 : a k 38*normalRep k 289=normalRep k 409 := by
  exact (walk_snoc k 35 [49, 71, 72] 38).symm
lemma arrow_span_289 (b : Fin 75) : a k b*normalRep k 289 ∈ normalSpan k := by
  by_cases h : arrowSource b=29
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [37, 38] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_289_37 k]
      exact normal_mem k 407
    · rw [extension_289_38 k]
      exact normal_mem k 409
  · rw [show a k b*normalRep k 289=0 from arrow_incompatible k b 35 29 [49, 71, 72] (normal_endpoints 289) h]
    exact Submodule.zero_mem _
lemma extension_290_69 : a k 69*normalRep k 290=normalRep k 410 := by
  exact (walk_snoc k 36 [50, 17, 21] 69).symm
lemma extension_290_70 : a k 70*normalRep k 290=normalRep k 411 := by
  exact (walk_snoc k 36 [50, 17, 21] 70).symm
lemma extension_290_71 : a k 71*normalRep k 290=0 := by
  change a k 71*walk k 36 [50, 17, 21]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_142 (a k) (relation_zero k) (e k 36)
lemma arrow_span_290 (b : Fin 75) : a k b*normalRep k 290 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_290_69 k]
      exact normal_mem k 410
    · rw [extension_290_70 k]
      exact normal_mem k 411
    · rw [extension_290_71 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 290=0 from arrow_incompatible k b 36 43 [50, 17, 21] (normal_endpoints 290) h]
    exact Submodule.zero_mem _
lemma extension_291_69 : a k 69*normalRep k 291=0 := by
  change a k 69*walk k 36 [51, 64, 36]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_163 (a k) (relation_zero k) (e k 36)
lemma extension_291_70 : a k 70*normalRep k 291=normalRep k 411 := by
  change a k 70*walk k 36 [51, 64, 36]=walk k 36 [50, 17, 21, 70]
  rw [← walk_snoc]
  exact Universal.mul_reduced_176 (a k) (relation_zero k) (e k 36)
lemma extension_291_71 : a k 71*normalRep k 291=normalRep k 412 := by
  exact (walk_snoc k 36 [51, 64, 36] 71).symm
lemma arrow_span_291 (b : Fin 75) : a k b*normalRep k 291 ∈ normalSpan k := by
  by_cases h : arrowSource b=43
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [69, 70, 71] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_291_69 k]
      exact Submodule.zero_mem _
    · rw [extension_291_70 k]
      exact normal_mem k 411
    · rw [extension_291_71 k]
      exact normal_mem k 412
  · rw [show a k b*normalRep k 291=0 from arrow_incompatible k b 36 43 [51, 64, 36] (normal_endpoints 291) h]
    exact Submodule.zero_mem _
lemma extension_292_47 : a k 47*normalRep k 292=normalRep k 413 := by
  exact (walk_snoc k 37 [52, 41, 43] 47).symm
lemma extension_292_48 : a k 48*normalRep k 292=normalRep k 414 := by
  exact (walk_snoc k 37 [52, 41, 43] 48).symm
lemma arrow_span_292 (b : Fin 75) : a k b*normalRep k 292 ∈ normalSpan k := by
  by_cases h : arrowSource b=34
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [47, 48] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_292_47 k]
      exact normal_mem k 413
    · rw [extension_292_48 k]
      exact normal_mem k 414
  · rw [show a k b*normalRep k 292=0 from arrow_incompatible k b 37 34 [52, 41, 43] (normal_endpoints 292) h]
    exact Submodule.zero_mem _
lemma extension_293_57 : a k 57*normalRep k 293=normalRep k 415 := by
  exact (walk_snoc k 37 [52, 41, 44] 57).symm
lemma extension_293_58 : a k 58*normalRep k 293=normalRep k 416 := by
  exact (walk_snoc k 37 [52, 41, 44] 58).symm
lemma extension_293_59 : a k 59*normalRep k 293=normalRep k 414 := by
  change a k 59*walk k 37 [52, 41, 44]=walk k 37 [52, 41, 43, 48]
  rw [← walk_snoc]
  exact Universal.mul_reduced_171 (a k) (relation_zero k) (e k 37)
lemma arrow_span_293 (b : Fin 75) : a k b*normalRep k 293 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_293_57 k]
      exact normal_mem k 415
    · rw [extension_293_58 k]
      exact normal_mem k 416
    · rw [extension_293_59 k]
      exact normal_mem k 414
  · rw [show a k b*normalRep k 293=0 from arrow_incompatible k b 37 39 [52, 41, 44] (normal_endpoints 293) h]
    exact Submodule.zero_mem _
lemma extension_294_6 : a k 6*normalRep k 294=normalRep k 413 := by
  change a k 6*walk k 37 [52, 42, 45]=walk k 37 [52, 41, 43, 47]
  rw [← walk_snoc]
  exact Universal.mul_reduced_172 (a k) (relation_zero k) (e k 37)
lemma arrow_span_294 (b : Fin 75) : a k b*normalRep k 294 ∈ normalSpan k := by
  by_cases h : arrowSource b=6
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [6] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_294_6 k]
      exact normal_mem k 413
  · rw [show a k b*normalRep k 294=0 from arrow_incompatible k b 37 6 [52, 42, 45] (normal_endpoints 294) h]
    exact Submodule.zero_mem _
lemma extension_295_1 : a k 1*normalRep k 295=normalRep k 417 := by
  exact (walk_snoc k 37 [53, 54, 15] 1).symm
lemma arrow_span_295 (b : Fin 75) : a k b*normalRep k 295 ∈ normalSpan k := by
  by_cases h : arrowSource b=1
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [1] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_295_1 k]
      exact normal_mem k 417
  · rw [show a k b*normalRep k 295=0 from arrow_incompatible k b 37 1 [53, 54, 15] (normal_endpoints 295) h]
    exact Submodule.zero_mem _
lemma extension_296_57 : a k 57*normalRep k 296=normalRep k 415 := by
  change a k 57*walk k 37 [53, 54, 16]=walk k 37 [52, 41, 44, 57]
  rw [← walk_snoc]
  exact Universal.mul_reduced_154 (a k) (relation_zero k) (e k 37)
lemma extension_296_58 : a k 58*normalRep k 296=normalRep k 417 := by
  change a k 58*walk k 37 [53, 54, 16]=walk k 37 [53, 54, 15, 1]
  rw [← walk_snoc]
  exact Universal.mul_reduced_129 (a k) (relation_zero k) (e k 37)
lemma extension_296_59 : a k 59*normalRep k 296=0 := by
  change a k 59*walk k 37 [53, 54, 16]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_131 (a k) (relation_zero k) (e k 37)
lemma arrow_span_296 (b : Fin 75) : a k b*normalRep k 296 ∈ normalSpan k := by
  by_cases h : arrowSource b=39
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [57, 58, 59] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rw [extension_296_57 k]
      exact normal_mem k 415
    · rw [extension_296_58 k]
      exact normal_mem k 417
    · rw [extension_296_59 k]
      exact Submodule.zero_mem _
  · rw [show a k b*normalRep k 296=0 from arrow_incompatible k b 37 39 [53, 54, 16] (normal_endpoints 296) h]
    exact Submodule.zero_mem _
lemma extension_297_33 : a k 33*normalRep k 297=0 := by
  change a k 33*walk k 38 [54, 15, 1]=0
  rw [← walk_snoc]
  exact Universal.mul_reduced_114 (a k) (relation_zero k) (e k 38)
lemma extension_297_34 : a k 34*normalRep k 297=normalRep k 418 := by
  exact (walk_snoc k 38 [54, 15, 1] 34).symm
lemma arrow_span_297 (b : Fin 75) : a k b*normalRep k 297 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_297_33 k]
      exact Submodule.zero_mem _
    · rw [extension_297_34 k]
      exact normal_mem k 418
  · rw [show a k b*normalRep k 297=0 from arrow_incompatible k b 38 26 [54, 15, 1] (normal_endpoints 297) h]
    exact Submodule.zero_mem _
lemma extension_298_5 : a k 5*normalRep k 298=normalRep k 418 := by
  change a k 5*walk k 38 [54, 16, 57]=walk k 38 [54, 15, 1, 34]
  rw [← walk_snoc]
  exact Universal.mul_reduced_189 (a k) (relation_zero k) (e k 38)
lemma arrow_span_298 (b : Fin 75) : a k b*normalRep k 298 ∈ normalSpan k := by
  by_cases h : arrowSource b=5
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [5] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl
    · rw [extension_298_5 k]
      exact normal_mem k 418
  · rw [show a k b*normalRep k 298=0 from arrow_incompatible k b 38 5 [54, 16, 57] (normal_endpoints 298) h]
    exact Submodule.zero_mem _
lemma extension_299_33 : a k 33*normalRep k 299=normalRep k 419 := by
  exact (walk_snoc k 38 [55, 27, 58] 33).symm
lemma extension_299_34 : a k 34*normalRep k 299=normalRep k 420 := by
  exact (walk_snoc k 38 [55, 27, 58] 34).symm
lemma arrow_span_299 (b : Fin 75) : a k b*normalRep k 299 ∈ normalSpan k := by
  by_cases h : arrowSource b=26
  · have hm := outgoing_spec b
    rw [h] at hm
    change b ∈ [33, 34] at hm
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · rw [extension_299_33 k]
      exact normal_mem k 419
    · rw [extension_299_34 k]
      exact normal_mem k 420
  · rw [show a k b*normalRep k 299=0 from arrow_incompatible k b 38 26 [55, 27, 58] (normal_endpoints 299) h]
    exact Submodule.zero_mem _
end UniserialComputations.N6.Presentation
