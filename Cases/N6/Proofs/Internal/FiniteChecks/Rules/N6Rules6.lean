import N6Rules5
noncomputable section
namespace UniserialComputations.N6.Presentation.Universal
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable {A : Type*} [Ring A] (v : Fin 75 → A) (H : ∀ z : Fin 47, polynomial v (relationTerms z)=0)
include H
lemma rule_313 : word v [18, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [19, 53, 54, 15]) (defining_0 v H)
  have h1 := congrArg (fun x : A => word v [33] * x) (rule_230 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_314 : word v [60, 4, 54, 15, 1, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [60, 4, 54, 15]) (defining_0 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_315 : word v [4, 54, 15, 1, 34, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [4, 54, 15]) (defining_1 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_316 : word v [52, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [53, 54, 15]) (defining_1 v H)
  have h1 := congrArg (fun x : A => word v [64] * x) (rule_291 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_317 : word v [17, 21, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_245 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_318 : word v [63, 21, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 70, 22]) (defining_2 v H)
  have h1 := congrArg (fun x : A => word v [39] * x) (rule_246 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_319 : word v [22, 3, 40, 62, 52, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [22]) (defining_3 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_320 : word v [8, 66, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_292 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_321 : word v [22, 3, 40, 60, 4, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [22, 3, 40, 60]) (defining_4 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_322 : word v [72, 37, 24, 19, 53, 55]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 25, 60]) (defining_4 v H)
  have h1 := congrArg (fun x : A => word v [55] * x) (rule_294 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_323 : word v [3, 40, 60, 4, 56, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [3, 40, 60]) (defining_5 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_324 : word v [37, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_192 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_279 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_325 : word v [66, 24, 18, 9, 41, 43]=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 25, 60]) (defining_5 v H)
  have h1 := congrArg (fun x : A => word v [56, 43] * x) (rule_193 v H)
  have h2 := congrArg (fun x : A => word v [43] * x) (rule_280 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1 + (-1) * h2
lemma rule_326 : word v [9, 41, 44, 57, 5, 64]=0 := by
  have h0 := congrArg (fun x : A => x * word v [9, 41, 44, 57]) (defining_6 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_327 : word v [4, 54, 15, 1, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [4, 54, 16, 57]) (defining_7 v H)
  have h1 := congrArg (fun x : A => word v [65] * x) (rule_287 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_328 : word v [9, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [9, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_329 : word v [52, 41, 44, 57, 5, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 44, 57]) (defining_7 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_330 : word v [13, 49, 69, 8, 68, 39]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69]) (defining_8 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_331 : word v [7, 17, 21, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_332 : word v [33, 13, 49, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_333 : word v [50, 17, 21, 69, 8, 67]=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 69]) (defining_9 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_334 : word v [14, 9, 41, 44, 58, 33]=0 := by
  have h0 := congrArg (fun x : A => x * word v [14]) (defining_10 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_335 : word v [8, 66, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 24, 18]) (defining_11 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_336 : word v [72, 37, 24, 18, 9, 42]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 24, 18]) (defining_11 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_337 : word v [24, 19, 53, 54, 15, 1] + (-word v [24, 18, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [24, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_282 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_338 : word v [29, 19, 53, 54, 15, 1] + (-word v [28, 14, 9, 41, 44, 58])=0 := by
  have h0 := congrArg (fun x : A => x * word v [29, 19, 53, 54]) (defining_12 v H)
  have h1 := congrArg (fun x : A => word v [58] * x) (rule_283 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_339 : (-word v [40, 60, 4, 54, 15, 1]) + word v [40, 60, 4, 54, 16, 58]=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 60, 4, 54]) (defining_12 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_340 : word v [24, 18, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [24, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_282 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_341 : word v [28, 14, 9, 41, 44, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [29, 19, 53, 54]) (defining_13 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_283 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_342 : word v [40, 60, 4, 54, 16, 59]=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 60, 4, 54]) (defining_13 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_343 : word v [41, 43, 47, 7, 17, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 47, 7]) (defining_14 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_344 : word v [55, 27, 58, 34, 63, 20]=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 59, 50]) (defining_14 v H)
  have h1 := congrArg (fun x : A => word v [20] * x) (rule_277 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_345 : (-word v [69, 8, 66, 24, 18, 9]) + word v [69, 8, 66, 24, 19, 52]=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 24]) (defining_16 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_346 : word v [70, 23, 66, 24, 18, 9] + (-word v [70, 22, 3, 40, 62, 52])=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 23, 66, 24]) (defining_16 v H)
  have h1 := congrArg (fun x : A => word v [52] * x) (rule_250 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_347 : word v [15, 1, 34, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [15, 1, 34, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_348 : word v [44, 57, 5, 63, 20, 31]=0 := by
  have h0 := congrArg (fun x : A => x * word v [44, 57, 5, 63]) (defining_17 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_349 : word v [27, 58, 34, 63, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 34, 63]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_350 : word v [43, 47, 7, 17, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 47, 7, 17]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_351 : word v [45, 6, 7, 17, 21, 71]=0 := by
  have h0 := congrArg (fun x : A => x * word v [45, 6, 7, 17]) (defining_18 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_352 : word v [7, 17, 21, 70, 22, 3] + (-word v [7, 17, 21, 69, 8, 68])=0 := by
  have h0 := congrArg (fun x : A => x * word v [7, 17, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_305 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_353 : word v [34, 63, 21, 70, 22, 3] + word v [33, 13, 49, 69, 8, 68]=0 := by
  have h0 := congrArg (fun x : A => x * word v [34, 63, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_307 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_354 : word v [50, 17, 21, 70, 22, 3] + (-word v [50, 17, 21, 69, 8, 68])=0 := by
  have h0 := congrArg (fun x : A => x * word v [50, 17, 21, 70]) (defining_20 v H)
  have h1 := congrArg (fun x : A => word v [68] * x) (rule_308 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_355 : word v [21, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_356 : word v [36, 70, 22, 3, 40, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 23, 66]) (defining_21 v H)
  have h1 := congrArg (fun x : A => word v [61] * x) (rule_303 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_357 : word v [49, 69, 8, 66, 25, 61]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66]) (defining_21 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_358 : (-word v [21, 69, 8, 66, 24, 19]) + word v [21, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [21, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_359 : word v [36, 70, 23, 66, 24, 19] + (-word v [36, 70, 22, 3, 40, 62])=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 70, 23, 66]) (defining_22 v H)
  have h1 := congrArg (fun x : A => word v [62] * x) (rule_303 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_360 : (-word v [49, 69, 8, 66, 24, 19]) + word v [49, 69, 8, 66, 25, 62]=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 69, 8, 66]) (defining_22 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_361 : word v [32, 61, 35, 55, 27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 55]) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_362 : word v [39, 12, 35, 55, 27, 57]=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 55]) (defining_24 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_363 : word v [36, 71, 72, 38, 28, 14] + (-word v [36, 70, 23, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [36, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_262 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_364 : word v [49, 71, 72, 38, 28, 14] + (-word v [49, 69, 8, 66, 24, 18])=0 := by
  have h0 := congrArg (fun x : A => x * word v [49, 71, 72, 38]) (defining_25 v H)
  have h1 := congrArg (fun x : A => word v [18] * x) (rule_263 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_365 : word v [74, 10, 11, 26, 31, 72]=0 := by
  have h0 := congrArg (fun x : A => x * word v [74, 10, 11, 26]) (defining_26 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_366 : word v [26, 31, 73, 67, 32, 60]=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 67]) (defining_27 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_367 : (-word v [35, 55, 27, 58, 33, 13]) + word v [35, 55, 27, 58, 34, 65]=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 58]) (defining_28 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_368 : word v [52, 41, 44, 58, 33, 13] + (-word v [52, 41, 43, 48, 51, 65])=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 44, 58]) (defining_28 v H)
  have h1 := congrArg (fun x : A => word v [65] * x) (rule_290 v H)
  have h2 := congrArg (fun x : A => word v [] * x) (rule_329 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1 + (1) * h2
lemma rule_369 : word v [73, 67, 32, 61, 35, 54]=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 61]) (defining_29 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_370 : word v [27, 58, 34, 63, 21, 69] + word v [27, 58, 33, 13, 49, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 34, 64]) (defining_30 v H)
  have h1 := congrArg (fun x : A => word v [69] * x) (rule_297 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_371 : word v [43, 48, 51, 64, 36, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 48, 51, 64]) (defining_30 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_372 : word v [46, 48, 51, 64, 36, 69]=0 := by
  have h0 := congrArg (fun x : A => x * word v [46, 48, 51, 64]) (defining_30 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_373 : (-word v [13, 49, 69, 8, 66, 24]) + word v [13, 49, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_311 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_374 : word v [63, 21, 69, 8, 66, 24] + word v [64, 36, 71, 72, 38, 29]=0 := by
  have h0 := congrArg (fun x : A => x * word v [64, 36, 71, 72]) (defining_31 v H)
  have h1 := congrArg (fun x : A => word v [24] * x) (rule_312 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_375 : word v [26, 31, 73, 68, 39, 12] + (-word v [26, 31, 73, 67, 32, 61])=0 := by
  have h0 := congrArg (fun x : A => x * word v [26, 31, 73, 68]) (defining_32 v H)
  have h1 := congrArg (fun x : A => word v [61] * x) (rule_302 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_376 : (-word v [67, 32, 61, 35, 56, 43]) + word v [67, 32, 62, 52, 42, 46]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 62, 52]) (defining_33 v H)
  have h1 := congrArg (fun x : A => word v [43] * x) (rule_281 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_377 : word v [32, 61, 35, 56, 43, 48] + (-word v [32, 61, 35, 55, 27, 59])=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 61, 35, 56]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_284 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_378 : word v [39, 12, 35, 56, 43, 48] + (-word v [39, 12, 35, 55, 27, 59])=0 := by
  have h0 := congrArg (fun x : A => x * word v [39, 12, 35, 56]) (defining_34 v H)
  have h1 := congrArg (fun x : A => word v [59] * x) (rule_285 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_379 : word v [32, 62, 52, 42, 45, 6] + (-word v [32, 61, 35, 56, 43, 47])=0 := by
  have h0 := congrArg (fun x : A => x * word v [32, 62, 52, 42]) (defining_35 v H)
  have h1 := congrArg (fun x : A => word v [47] * x) (rule_266 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_380 : word v [40, 62, 52, 42, 45, 6] + (-word v [39, 12, 35, 56, 43, 47])=0 := by
  have h0 := congrArg (fun x : A => x * word v [40, 62, 52, 42]) (defining_35 v H)
  have h1 := congrArg (fun x : A => word v [47] * x) (rule_267 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_381 : word v [12, 35, 56, 43, 47, 7] + (-word v [12, 35, 55, 27, 59, 50])=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 56, 43]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [50] * x) (rule_268 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_382 : word v [61, 35, 56, 43, 47, 7] + (-word v [61, 35, 55, 27, 59, 50])=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 56, 43]) (defining_36 v H)
  have h1 := congrArg (fun x : A => word v [50] * x) (rule_270 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_383 : word v [27, 58, 33, 13, 49, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [27, 58, 33, 13]) (defining_37 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0
lemma rule_384 : (-word v [43, 47, 7, 17, 21, 70]) + word v [43, 48, 51, 64, 36, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [43, 48, 51, 65]) (defining_37 v H)
  have h1 := congrArg (fun x : A => word v [70] * x) (rule_298 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_385 : (-word v [45, 6, 7, 17, 21, 70]) + word v [46, 48, 51, 64, 36, 70]=0 := by
  have h0 := congrArg (fun x : A => x * word v [46, 48, 51, 65]) (defining_37 v H)
  have h1 := congrArg (fun x : A => word v [70] * x) (rule_300 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_386 : word v [35, 55, 27, 59, 50, 17] + (-word v [35, 55, 27, 58, 34, 63])=0 := by
  have h0 := congrArg (fun x : A => x * word v [35, 55, 27, 59]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [63] * x) (rule_289 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_387 : (-word v [52, 41, 43, 47, 7, 17]) + word v [52, 41, 43, 48, 51, 63]=0 := by
  have h0 := congrArg (fun x : A => x * word v [52, 41, 43, 48]) (defining_38 v H)
  have h1 := congrArg (fun x : A => word v [17] * x) (rule_273 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_388 : (-word v [8, 66, 24, 18, 9, 41]) + word v [8, 66, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [8, 66, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_237 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_389 : word v [22, 3, 40, 62, 52, 41] + (-word v [22, 3, 40, 60, 4, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [22, 3, 40, 62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_293 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_390 : (-word v [72, 37, 24, 18, 9, 41]) + word v [72, 37, 24, 19, 53, 56]=0 := by
  have h0 := congrArg (fun x : A => x * word v [72, 37, 24, 19]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [41] * x) (rule_239 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_391 : word v [73, 67, 32, 62, 52, 41] + (-word v [73, 67, 32, 61, 35, 56])=0 := by
  have h0 := congrArg (fun x : A => x * word v [73, 67, 32, 62]) (defining_39 v H)
  have h1 := congrArg (fun x : A => word v [56] * x) (rule_295 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_392 : (-word v [3, 40, 60, 4, 54, 16]) + word v [3, 40, 60, 4, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [3, 40, 60, 4]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_215 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_393 : word v [37, 24, 19, 53, 54, 16] + (-word v [37, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [37, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_216 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_279 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_394 : word v [66, 24, 19, 53, 54, 16] + (-word v [66, 24, 18, 9, 41, 44])=0 := by
  have h0 := congrArg (fun x : A => x * word v [66, 24, 19, 53]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [27] * x) (rule_217 v H)
  have h2 := congrArg (fun x : A => word v [44] * x) (rule_280 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_395 : (-word v [67, 32, 61, 35, 55, 27]) + word v [67, 32, 61, 35, 56, 44]=0 := by
  have h0 := congrArg (fun x : A => x * word v [67, 32, 61, 35]) (defining_40 v H)
  have h1 := congrArg (fun x : A => word v [16] * x) (rule_259 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_396 : (-word v [12, 35, 55, 27, 58, 34]) + word v [12, 35, 55, 27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [12, 35, 55, 27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_252 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_397 : (-word v [14, 9, 41, 44, 57, 5]) + word v [14, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [14, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_269 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_398 : (-word v [18, 9, 41, 44, 57, 5]) + word v [18, 9, 41, 44, 58, 34]=0 := by
  have h0 := congrArg (fun x : A => x * word v [18, 9, 41, 44]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [51] * x) (rule_232 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_399 : word v [60, 4, 54, 16, 57, 5] + (-word v [60, 4, 54, 15, 1, 34])=0 := by
  have h0 := congrArg (fun x : A => x * word v [60, 4, 54, 16]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [34] * x) (rule_231 v H)
  have h2 := congrArg (fun x : A => word v [51] * x) (rule_233 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_400 : (-word v [61, 35, 55, 27, 58, 34]) + word v [61, 35, 55, 27, 59, 51]=0 := by
  have h0 := congrArg (fun x : A => x * word v [61, 35, 55, 27]) (defining_41 v H)
  have h1 := congrArg (fun x : A => word v [5] * x) (rule_253 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_401 : (-word v [31, 73, 67, 32, 61, 35]) + word v [31, 73, 67, 32, 62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v [31, 73, 67, 32]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [4] * x) (rule_256 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_402 : word v [69, 8, 66, 25, 60, 4] + (-word v [69, 8, 66, 24, 19, 53])=0 := by
  have h0 := congrArg (fun x : A => x * word v [69, 8, 66, 25]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_247 v H)
  have h2 := congrArg (fun x : A => word v [53] * x) (rule_249 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_403 : (-word v [70, 22, 3, 40, 60, 4]) + word v [70, 22, 3, 40, 62, 53]=0 := by
  have h0 := congrArg (fun x : A => x * word v [70, 22, 3, 40]) (defining_42 v H)
  have h1 := congrArg (fun x : A => word v [35] * x) (rule_248 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_404 : word v [41, 43, 47, 7, 17, 21] + (-word v [41, 43, 48, 51, 64, 36]) + word v [41, 43, 48, 51, 65, 49]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 43, 48, 51]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [21] * x) (rule_276 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_405 : word v [41, 44, 57, 5, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [41, 44, 57, 5]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_220 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_221 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_406 : word v [54, 15, 1, 34, 63, 21]=0 := by
  have h0 := congrArg (fun x : A => x * word v [54, 15, 1, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [36] * x) (rule_211 v H)
  have h2 := congrArg (fun x : A => word v [49] * x) (rule_222 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (-1) * h2
lemma rule_407 : (-word v [55, 27, 58, 34, 63, 21]) + word v [55, 27, 58, 34, 64, 36] + (-word v [55, 27, 58, 33, 13, 49])=0 := by
  have h0 := congrArg (fun x : A => x * word v [55, 27, 58, 34]) (defining_43 v H)
  have h1 := congrArg (fun x : A => word v [49] * x) (rule_258 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_408 : (-word v [11, 26, 31, 73, 67, 32]) + word v [11, 26, 31, 73, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [11, 26, 31, 73]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [25] * x) (rule_310 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (-1) * h1
lemma rule_409 : word v [13, 49, 69, 8, 66, 25] + word v [13, 49, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [13, 49, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_224 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_410 : word v [17, 21, 69, 8, 66, 25] + word v [17, 21, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [17, 21, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_225 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_411 : word v [63, 21, 69, 8, 66, 25] + word v [63, 21, 69, 8, 68, 40]=0 := by
  have h0 := congrArg (fun x : A => x * word v [63, 21, 69, 8]) (defining_44 v H)
  have h1 := congrArg (fun x : A => word v [32] * x) (rule_226 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_412 : word v [6, 7, 17, 21, 69, 8] + word v [6, 7, 17, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [6, 7, 17, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [73] * x) (rule_242 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_413 : word v [47, 7, 17, 21, 69, 8] + word v [47, 7, 17, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [47, 7, 17, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [73] * x) (rule_243 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_414 : word v [48, 51, 64, 36, 71, 73] + word v [47, 7, 17, 21, 69, 8]=0 := by
  have h0 := congrArg (fun x : A => x * word v [48, 51, 64, 36]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_260 v H)
  have h2 := congrArg (fun x : A => word v [23] * x) (rule_274 v H)
  have h3 := congrArg (fun x : A => word v [] * x) (rule_413 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1 + (1) * h2 + (1) * h3
lemma rule_415 : (-word v [58, 33, 13, 49, 69, 8]) + word v [58, 33, 13, 49, 71, 73]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 33, 13, 49]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [23] * x) (rule_275 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_416 : (-word v [58, 33, 13, 49, 69, 8]) + word v [58, 34, 63, 21, 70, 23]=0 := by
  have h0 := congrArg (fun x : A => x * word v [58, 34, 63, 21]) (defining_45 v H)
  have h1 := congrArg (fun x : A => word v [8] * x) (rule_261 v H)
  have h2 := congrArg (fun x : A => word v [73] * x) (rule_244 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (-1) * h1 + (1) * h2
lemma rule_417 : word v [10, 11, 26, 31, 73, 66]=0 := by
  have h0 := congrArg (fun x : A => x * word v [10, 11, 26, 31]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [37] * x) (rule_255 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (1) * h0 + (1) * h1
lemma rule_418 : word v [33, 13, 49, 71, 72, 37] + (-word v [33, 13, 49, 69, 8, 66])=0 := by
  have h0 := congrArg (fun x : A => x * word v [33, 13, 49, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_306 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
lemma rule_419 : word v [51, 64, 36, 71, 72, 37] + word v [50, 17, 21, 69, 8, 66]=0 := by
  have h0 := congrArg (fun x : A => x * word v [51, 64, 36, 71]) (defining_46 v H)
  have h1 := congrArg (fun x : A => word v [66] * x) (rule_309 v H)
  simp only [word,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_zero,zero_mul] at *
  linear_combination (norm := noncomm_ring) (-1) * h0 + (1) * h1
end UniserialComputations.N6.Presentation.Universal
noncomputable section
namespace UniserialComputations.N6.Presentation
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
variable (k : Type*) [Field k]
lemma rule_313 : word (a k) [18, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_313 (a k) (relation_zero k)
lemma rule_314 : word (a k) [60, 4, 54, 15, 1, 33]=0 := by
  exact Universal.rule_314 (a k) (relation_zero k)
lemma rule_315 : word (a k) [4, 54, 15, 1, 34, 64]=0 := by
  exact Universal.rule_315 (a k) (relation_zero k)
lemma rule_316 : word (a k) [52, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_316 (a k) (relation_zero k)
lemma rule_317 : word (a k) [17, 21, 69, 8, 68, 39]=0 := by
  exact Universal.rule_317 (a k) (relation_zero k)
lemma rule_318 : word (a k) [63, 21, 69, 8, 68, 39]=0 := by
  exact Universal.rule_318 (a k) (relation_zero k)
lemma rule_319 : word (a k) [22, 3, 40, 62, 52, 42]=0 := by
  exact Universal.rule_319 (a k) (relation_zero k)
lemma rule_320 : word (a k) [8, 66, 24, 19, 53, 55]=0 := by
  exact Universal.rule_320 (a k) (relation_zero k)
lemma rule_321 : word (a k) [22, 3, 40, 60, 4, 55]=0 := by
  exact Universal.rule_321 (a k) (relation_zero k)
lemma rule_322 : word (a k) [72, 37, 24, 19, 53, 55]=0 := by
  exact Universal.rule_322 (a k) (relation_zero k)
lemma rule_323 : word (a k) [3, 40, 60, 4, 56, 43]=0 := by
  exact Universal.rule_323 (a k) (relation_zero k)
lemma rule_324 : word (a k) [37, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_324 (a k) (relation_zero k)
lemma rule_325 : word (a k) [66, 24, 18, 9, 41, 43]=0 := by
  exact Universal.rule_325 (a k) (relation_zero k)
lemma rule_326 : word (a k) [9, 41, 44, 57, 5, 64]=0 := by
  exact Universal.rule_326 (a k) (relation_zero k)
lemma rule_327 : word (a k) [4, 54, 15, 1, 34, 65]=0 := by
  exact Universal.rule_327 (a k) (relation_zero k)
lemma rule_328 : word (a k) [9, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_328 (a k) (relation_zero k)
lemma rule_329 : word (a k) [52, 41, 44, 57, 5, 65]=0 := by
  exact Universal.rule_329 (a k) (relation_zero k)
lemma rule_330 : word (a k) [13, 49, 69, 8, 68, 39]=0 := by
  exact Universal.rule_330 (a k) (relation_zero k)
lemma rule_331 : word (a k) [7, 17, 21, 69, 8, 67]=0 := by
  exact Universal.rule_331 (a k) (relation_zero k)
lemma rule_332 : word (a k) [33, 13, 49, 69, 8, 67]=0 := by
  exact Universal.rule_332 (a k) (relation_zero k)
lemma rule_333 : word (a k) [50, 17, 21, 69, 8, 67]=0 := by
  exact Universal.rule_333 (a k) (relation_zero k)
lemma rule_334 : word (a k) [14, 9, 41, 44, 58, 33]=0 := by
  exact Universal.rule_334 (a k) (relation_zero k)
lemma rule_335 : word (a k) [8, 66, 24, 18, 9, 42]=0 := by
  exact Universal.rule_335 (a k) (relation_zero k)
lemma rule_336 : word (a k) [72, 37, 24, 18, 9, 42]=0 := by
  exact Universal.rule_336 (a k) (relation_zero k)
lemma rule_337 : word (a k) [24, 19, 53, 54, 15, 1] + (-word (a k) [24, 18, 9, 41, 44, 58])=0 := by
  exact Universal.rule_337 (a k) (relation_zero k)
lemma rule_338 : word (a k) [29, 19, 53, 54, 15, 1] + (-word (a k) [28, 14, 9, 41, 44, 58])=0 := by
  exact Universal.rule_338 (a k) (relation_zero k)
lemma rule_339 : (-word (a k) [40, 60, 4, 54, 15, 1]) + word (a k) [40, 60, 4, 54, 16, 58]=0 := by
  exact Universal.rule_339 (a k) (relation_zero k)
lemma rule_340 : word (a k) [24, 18, 9, 41, 44, 59]=0 := by
  exact Universal.rule_340 (a k) (relation_zero k)
lemma rule_341 : word (a k) [28, 14, 9, 41, 44, 59]=0 := by
  exact Universal.rule_341 (a k) (relation_zero k)
lemma rule_342 : word (a k) [40, 60, 4, 54, 16, 59]=0 := by
  exact Universal.rule_342 (a k) (relation_zero k)
lemma rule_343 : word (a k) [41, 43, 47, 7, 17, 20]=0 := by
  exact Universal.rule_343 (a k) (relation_zero k)
lemma rule_344 : word (a k) [55, 27, 58, 34, 63, 20]=0 := by
  exact Universal.rule_344 (a k) (relation_zero k)
lemma rule_345 : (-word (a k) [69, 8, 66, 24, 18, 9]) + word (a k) [69, 8, 66, 24, 19, 52]=0 := by
  exact Universal.rule_345 (a k) (relation_zero k)
lemma rule_346 : word (a k) [70, 23, 66, 24, 18, 9] + (-word (a k) [70, 22, 3, 40, 62, 52])=0 := by
  exact Universal.rule_346 (a k) (relation_zero k)
lemma rule_347 : word (a k) [15, 1, 34, 63, 20, 31]=0 := by
  exact Universal.rule_347 (a k) (relation_zero k)
lemma rule_348 : word (a k) [44, 57, 5, 63, 20, 31]=0 := by
  exact Universal.rule_348 (a k) (relation_zero k)
lemma rule_349 : word (a k) [27, 58, 34, 63, 21, 71]=0 := by
  exact Universal.rule_349 (a k) (relation_zero k)
lemma rule_350 : word (a k) [43, 47, 7, 17, 21, 71]=0 := by
  exact Universal.rule_350 (a k) (relation_zero k)
lemma rule_351 : word (a k) [45, 6, 7, 17, 21, 71]=0 := by
  exact Universal.rule_351 (a k) (relation_zero k)
lemma rule_352 : word (a k) [7, 17, 21, 70, 22, 3] + (-word (a k) [7, 17, 21, 69, 8, 68])=0 := by
  exact Universal.rule_352 (a k) (relation_zero k)
lemma rule_353 : word (a k) [34, 63, 21, 70, 22, 3] + word (a k) [33, 13, 49, 69, 8, 68]=0 := by
  exact Universal.rule_353 (a k) (relation_zero k)
lemma rule_354 : word (a k) [50, 17, 21, 70, 22, 3] + (-word (a k) [50, 17, 21, 69, 8, 68])=0 := by
  exact Universal.rule_354 (a k) (relation_zero k)
lemma rule_355 : word (a k) [21, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_355 (a k) (relation_zero k)
lemma rule_356 : word (a k) [36, 70, 22, 3, 40, 61]=0 := by
  exact Universal.rule_356 (a k) (relation_zero k)
lemma rule_357 : word (a k) [49, 69, 8, 66, 25, 61]=0 := by
  exact Universal.rule_357 (a k) (relation_zero k)
lemma rule_358 : (-word (a k) [21, 69, 8, 66, 24, 19]) + word (a k) [21, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_358 (a k) (relation_zero k)
lemma rule_359 : word (a k) [36, 70, 23, 66, 24, 19] + (-word (a k) [36, 70, 22, 3, 40, 62])=0 := by
  exact Universal.rule_359 (a k) (relation_zero k)
lemma rule_360 : (-word (a k) [49, 69, 8, 66, 24, 19]) + word (a k) [49, 69, 8, 66, 25, 62]=0 := by
  exact Universal.rule_360 (a k) (relation_zero k)
lemma rule_361 : word (a k) [32, 61, 35, 55, 27, 57]=0 := by
  exact Universal.rule_361 (a k) (relation_zero k)
lemma rule_362 : word (a k) [39, 12, 35, 55, 27, 57]=0 := by
  exact Universal.rule_362 (a k) (relation_zero k)
lemma rule_363 : word (a k) [36, 71, 72, 38, 28, 14] + (-word (a k) [36, 70, 23, 66, 24, 18])=0 := by
  exact Universal.rule_363 (a k) (relation_zero k)
lemma rule_364 : word (a k) [49, 71, 72, 38, 28, 14] + (-word (a k) [49, 69, 8, 66, 24, 18])=0 := by
  exact Universal.rule_364 (a k) (relation_zero k)
lemma rule_365 : word (a k) [74, 10, 11, 26, 31, 72]=0 := by
  exact Universal.rule_365 (a k) (relation_zero k)
lemma rule_366 : word (a k) [26, 31, 73, 67, 32, 60]=0 := by
  exact Universal.rule_366 (a k) (relation_zero k)
lemma rule_367 : (-word (a k) [35, 55, 27, 58, 33, 13]) + word (a k) [35, 55, 27, 58, 34, 65]=0 := by
  exact Universal.rule_367 (a k) (relation_zero k)
lemma rule_368 : word (a k) [52, 41, 44, 58, 33, 13] + (-word (a k) [52, 41, 43, 48, 51, 65])=0 := by
  exact Universal.rule_368 (a k) (relation_zero k)
lemma rule_369 : word (a k) [73, 67, 32, 61, 35, 54]=0 := by
  exact Universal.rule_369 (a k) (relation_zero k)
lemma rule_370 : word (a k) [27, 58, 34, 63, 21, 69] + word (a k) [27, 58, 33, 13, 49, 69]=0 := by
  exact Universal.rule_370 (a k) (relation_zero k)
lemma rule_371 : word (a k) [43, 48, 51, 64, 36, 69]=0 := by
  exact Universal.rule_371 (a k) (relation_zero k)
lemma rule_372 : word (a k) [46, 48, 51, 64, 36, 69]=0 := by
  exact Universal.rule_372 (a k) (relation_zero k)
lemma rule_373 : (-word (a k) [13, 49, 69, 8, 66, 24]) + word (a k) [13, 49, 71, 72, 38, 29]=0 := by
  exact Universal.rule_373 (a k) (relation_zero k)
lemma rule_374 : word (a k) [63, 21, 69, 8, 66, 24] + word (a k) [64, 36, 71, 72, 38, 29]=0 := by
  exact Universal.rule_374 (a k) (relation_zero k)
lemma rule_375 : word (a k) [26, 31, 73, 68, 39, 12] + (-word (a k) [26, 31, 73, 67, 32, 61])=0 := by
  exact Universal.rule_375 (a k) (relation_zero k)
lemma rule_376 : (-word (a k) [67, 32, 61, 35, 56, 43]) + word (a k) [67, 32, 62, 52, 42, 46]=0 := by
  exact Universal.rule_376 (a k) (relation_zero k)
lemma rule_377 : word (a k) [32, 61, 35, 56, 43, 48] + (-word (a k) [32, 61, 35, 55, 27, 59])=0 := by
  exact Universal.rule_377 (a k) (relation_zero k)
lemma rule_378 : word (a k) [39, 12, 35, 56, 43, 48] + (-word (a k) [39, 12, 35, 55, 27, 59])=0 := by
  exact Universal.rule_378 (a k) (relation_zero k)
lemma rule_379 : word (a k) [32, 62, 52, 42, 45, 6] + (-word (a k) [32, 61, 35, 56, 43, 47])=0 := by
  exact Universal.rule_379 (a k) (relation_zero k)
lemma rule_380 : word (a k) [40, 62, 52, 42, 45, 6] + (-word (a k) [39, 12, 35, 56, 43, 47])=0 := by
  exact Universal.rule_380 (a k) (relation_zero k)
lemma rule_381 : word (a k) [12, 35, 56, 43, 47, 7] + (-word (a k) [12, 35, 55, 27, 59, 50])=0 := by
  exact Universal.rule_381 (a k) (relation_zero k)
lemma rule_382 : word (a k) [61, 35, 56, 43, 47, 7] + (-word (a k) [61, 35, 55, 27, 59, 50])=0 := by
  exact Universal.rule_382 (a k) (relation_zero k)
lemma rule_383 : word (a k) [27, 58, 33, 13, 49, 70]=0 := by
  exact Universal.rule_383 (a k) (relation_zero k)
lemma rule_384 : (-word (a k) [43, 47, 7, 17, 21, 70]) + word (a k) [43, 48, 51, 64, 36, 70]=0 := by
  exact Universal.rule_384 (a k) (relation_zero k)
lemma rule_385 : (-word (a k) [45, 6, 7, 17, 21, 70]) + word (a k) [46, 48, 51, 64, 36, 70]=0 := by
  exact Universal.rule_385 (a k) (relation_zero k)
lemma rule_386 : word (a k) [35, 55, 27, 59, 50, 17] + (-word (a k) [35, 55, 27, 58, 34, 63])=0 := by
  exact Universal.rule_386 (a k) (relation_zero k)
lemma rule_387 : (-word (a k) [52, 41, 43, 47, 7, 17]) + word (a k) [52, 41, 43, 48, 51, 63]=0 := by
  exact Universal.rule_387 (a k) (relation_zero k)
lemma rule_388 : (-word (a k) [8, 66, 24, 18, 9, 41]) + word (a k) [8, 66, 24, 19, 53, 56]=0 := by
  exact Universal.rule_388 (a k) (relation_zero k)
lemma rule_389 : word (a k) [22, 3, 40, 62, 52, 41] + (-word (a k) [22, 3, 40, 60, 4, 56])=0 := by
  exact Universal.rule_389 (a k) (relation_zero k)
lemma rule_390 : (-word (a k) [72, 37, 24, 18, 9, 41]) + word (a k) [72, 37, 24, 19, 53, 56]=0 := by
  exact Universal.rule_390 (a k) (relation_zero k)
lemma rule_391 : word (a k) [73, 67, 32, 62, 52, 41] + (-word (a k) [73, 67, 32, 61, 35, 56])=0 := by
  exact Universal.rule_391 (a k) (relation_zero k)
lemma rule_392 : (-word (a k) [3, 40, 60, 4, 54, 16]) + word (a k) [3, 40, 60, 4, 56, 44]=0 := by
  exact Universal.rule_392 (a k) (relation_zero k)
lemma rule_393 : word (a k) [37, 24, 19, 53, 54, 16] + (-word (a k) [37, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_393 (a k) (relation_zero k)
lemma rule_394 : word (a k) [66, 24, 19, 53, 54, 16] + (-word (a k) [66, 24, 18, 9, 41, 44])=0 := by
  exact Universal.rule_394 (a k) (relation_zero k)
lemma rule_395 : (-word (a k) [67, 32, 61, 35, 55, 27]) + word (a k) [67, 32, 61, 35, 56, 44]=0 := by
  exact Universal.rule_395 (a k) (relation_zero k)
lemma rule_396 : (-word (a k) [12, 35, 55, 27, 58, 34]) + word (a k) [12, 35, 55, 27, 59, 51]=0 := by
  exact Universal.rule_396 (a k) (relation_zero k)
lemma rule_397 : (-word (a k) [14, 9, 41, 44, 57, 5]) + word (a k) [14, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_397 (a k) (relation_zero k)
lemma rule_398 : (-word (a k) [18, 9, 41, 44, 57, 5]) + word (a k) [18, 9, 41, 44, 58, 34]=0 := by
  exact Universal.rule_398 (a k) (relation_zero k)
lemma rule_399 : word (a k) [60, 4, 54, 16, 57, 5] + (-word (a k) [60, 4, 54, 15, 1, 34])=0 := by
  exact Universal.rule_399 (a k) (relation_zero k)
lemma rule_400 : (-word (a k) [61, 35, 55, 27, 58, 34]) + word (a k) [61, 35, 55, 27, 59, 51]=0 := by
  exact Universal.rule_400 (a k) (relation_zero k)
lemma rule_401 : (-word (a k) [31, 73, 67, 32, 61, 35]) + word (a k) [31, 73, 67, 32, 62, 53]=0 := by
  exact Universal.rule_401 (a k) (relation_zero k)
lemma rule_402 : word (a k) [69, 8, 66, 25, 60, 4] + (-word (a k) [69, 8, 66, 24, 19, 53])=0 := by
  exact Universal.rule_402 (a k) (relation_zero k)
lemma rule_403 : (-word (a k) [70, 22, 3, 40, 60, 4]) + word (a k) [70, 22, 3, 40, 62, 53]=0 := by
  exact Universal.rule_403 (a k) (relation_zero k)
lemma rule_404 : word (a k) [41, 43, 47, 7, 17, 21] + (-word (a k) [41, 43, 48, 51, 64, 36]) + word (a k) [41, 43, 48, 51, 65, 49]=0 := by
  exact Universal.rule_404 (a k) (relation_zero k)
lemma rule_405 : word (a k) [41, 44, 57, 5, 63, 21]=0 := by
  exact Universal.rule_405 (a k) (relation_zero k)
lemma rule_406 : word (a k) [54, 15, 1, 34, 63, 21]=0 := by
  exact Universal.rule_406 (a k) (relation_zero k)
lemma rule_407 : (-word (a k) [55, 27, 58, 34, 63, 21]) + word (a k) [55, 27, 58, 34, 64, 36] + (-word (a k) [55, 27, 58, 33, 13, 49])=0 := by
  exact Universal.rule_407 (a k) (relation_zero k)
lemma rule_408 : (-word (a k) [11, 26, 31, 73, 67, 32]) + word (a k) [11, 26, 31, 73, 68, 40]=0 := by
  exact Universal.rule_408 (a k) (relation_zero k)
lemma rule_409 : word (a k) [13, 49, 69, 8, 66, 25] + word (a k) [13, 49, 69, 8, 68, 40]=0 := by
  exact Universal.rule_409 (a k) (relation_zero k)
lemma rule_410 : word (a k) [17, 21, 69, 8, 66, 25] + word (a k) [17, 21, 69, 8, 68, 40]=0 := by
  exact Universal.rule_410 (a k) (relation_zero k)
lemma rule_411 : word (a k) [63, 21, 69, 8, 66, 25] + word (a k) [63, 21, 69, 8, 68, 40]=0 := by
  exact Universal.rule_411 (a k) (relation_zero k)
lemma rule_412 : word (a k) [6, 7, 17, 21, 69, 8] + word (a k) [6, 7, 17, 21, 70, 23]=0 := by
  exact Universal.rule_412 (a k) (relation_zero k)
lemma rule_413 : word (a k) [47, 7, 17, 21, 69, 8] + word (a k) [47, 7, 17, 21, 70, 23]=0 := by
  exact Universal.rule_413 (a k) (relation_zero k)
lemma rule_414 : word (a k) [48, 51, 64, 36, 71, 73] + word (a k) [47, 7, 17, 21, 69, 8]=0 := by
  exact Universal.rule_414 (a k) (relation_zero k)
lemma rule_415 : (-word (a k) [58, 33, 13, 49, 69, 8]) + word (a k) [58, 33, 13, 49, 71, 73]=0 := by
  exact Universal.rule_415 (a k) (relation_zero k)
lemma rule_416 : (-word (a k) [58, 33, 13, 49, 69, 8]) + word (a k) [58, 34, 63, 21, 70, 23]=0 := by
  exact Universal.rule_416 (a k) (relation_zero k)
lemma rule_417 : word (a k) [10, 11, 26, 31, 73, 66]=0 := by
  exact Universal.rule_417 (a k) (relation_zero k)
lemma rule_418 : word (a k) [33, 13, 49, 71, 72, 37] + (-word (a k) [33, 13, 49, 69, 8, 66])=0 := by
  exact Universal.rule_418 (a k) (relation_zero k)
lemma rule_419 : word (a k) [51, 64, 36, 71, 72, 37] + word (a k) [50, 17, 21, 69, 8, 66]=0 := by
  exact Universal.rule_419 (a k) (relation_zero k)
end UniserialComputations.N6.Presentation
